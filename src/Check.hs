{-# LANGUAGE LambdaCase, OverloadedStrings, TemplateHaskell, TupleSections
  , TypeSynonymInstances, FlexibleInstances, RankNTypes, FlexibleContexts
  , DataKinds #-}

module Check (typecheck) where

import Prelude hiding (span)
import Control.Lens
    ((<<+=), assign, makeLenses, over, use, view, views, locally, mapped)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Bifunctor
import Data.Foldable
import Data.Graph (SCC(..), flattenSCC, stronglyConnComp)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)

import Misc
import SrcPos
import FreeVars
import Subst
import NonEmpty
import qualified Ast
import Ast (Id(..), IdCase(..), idstr, scmBody)
import TypeErr
import AnnotAst
import Match
import Desugar
import qualified DesugaredAst

data Env = Env
    { _envDefs :: Map String Scheme
    -- | Maps a constructor to its variant index in the type definition it
    --   constructs, the signature/left-hand-side of the type definition, the
    --   types of its parameters, and the span (number of constructors) of the
    --   datatype
    , _envCtors :: Map String (VariantIx, (String, [TVar]), [Type], Span)
    , _envTypeDefs :: Map String ([TVar], [(String, [Type])])
    }
makeLenses ''Env

data St = St
    { _tvCount :: Int
    , _substs :: Subst
    }
    deriving (Show)
makeLenses ''St

-- | Type checker monad
type Infer a = ReaderT Env (StateT St (Except TypeErr)) a


typecheck :: Ast.Program -> Either TypeErr DesugaredAst.Program
typecheck prog = runExcept $ do
    (inferred, St _ substs) <- runInfer (inferProgram prog)
    let inferred' = substProgram substs inferred
    pure (unsugar inferred')

runInfer :: Infer a -> Except TypeErr (a, St)
runInfer m = runStateT (runReaderT m initEnv) initSt

initEnv :: Env
initEnv = Env
    { _envDefs = Map.empty
    , _envCtors = Map.empty
    , _envTypeDefs = Map.empty
    }

initSt :: St
initSt = St { _tvCount = 0, _substs = Map.empty }

fresh :: Infer Type
fresh = fmap TVar fresh'

fresh' :: Infer TVar
fresh' = fmap TVImplicit fresh''

fresh'' :: Infer Int
fresh'' = tvCount <<+= 1

withLocals :: [(String, Scheme)] -> Infer a -> Infer a
withLocals = withLocals' . Map.fromList

withLocals' :: Map String Scheme -> Infer a -> Infer a
withLocals' = augment envDefs

withLocal :: (String, Scheme) -> Infer a -> Infer a
withLocal b = locally envDefs (uncurry Map.insert b)

-- Inference
--------------------------------------------------------------------------------
inferProgram :: Ast.Program -> Infer Program
inferProgram (Ast.Program defs tdefs externs) = do
    (_, (WithPos mainPos _)) <- maybe
        (throwError MainNotDefined)
        pure
        (lookup "main" (map (first idstr) defs))
    (tdefs', ctors) <- checkTypeDefs tdefs
    augment envTypeDefs tdefs' $ augment envCtors ctors $ do
        externs' <- checkExterns externs
        let externs'' = fmap (Forall Set.empty) externs'
        defs' <- augment envDefs externs'' (inferDefs defs)
        let (Forall _ mainT, main) = fromJust (Map.lookup "main" defs')
        let expectedMainType = TFun (TPrim TUnit) (TPrim TUnit)
        unify (Expected expectedMainType) (Found mainPos mainT)
        let defs'' = Map.delete "main" defs'
        let tdefs'' = fmap (second (map snd)) tdefs'
        pure (Program main defs'' tdefs'' externs')

checkExterns :: [Ast.Extern] -> Infer (Map String Type)
checkExterns = fmap Map.fromList . mapM checkExtern

checkExtern :: Ast.Extern -> Infer (String, Type)
checkExtern (Ast.Extern name t) = case Set.lookupMin (ftv t) of
    Just tv -> throwError (ExternNotMonomorphic name tv)
    Nothing -> pure (idstr name, t)

checkTypeDefs
    :: [Ast.TypeDef]
    -> Infer
           ( Map String ([TVar], [(String, [Type])])
           , Map String (VariantIx, (String, [TVar]), [Type], Span)
           )
checkTypeDefs tdefs = do
    (tdefs', ctors) <- checkTypeDefsNoConflicting tdefs
    forM_ (Map.toList tdefs') (assertNoRec tdefs')
    pure (fmap (second (map snd)) tdefs', ctors)
  where
    -- | Check that type definitions are not recursive without indirection and
    --   that constructors don't refer to undefined types.
    assertNoRec tds (x, (_, cs)) = assertNoRecCtors tds x Map.empty cs
    assertNoRecCtors tds x s =
        mapM_ $ \(cpos, (_, ts)) ->
            forM_ ts (assertNoRecType tds x cpos . subst s)
    assertNoRecType tds x cpos = \case
        TVar _ -> pure ()
        TPrim _ -> pure ()
        TConst (y, ts) -> if x == y
            then throwError (RecTypeDef x cpos)
            else case Map.lookup y tds of
                Just (tvs, cs) ->
                    let substs = Map.fromList (zip tvs ts)
                    in assertNoRecCtors tds x substs cs
                Nothing -> throwError (UndefType cpos y)
        TFun _ _ -> pure ()
        TBox _ -> pure ()

-- | Check that there are no conflicting type names or constructor names.
checkTypeDefsNoConflicting
    :: [Ast.TypeDef]
    -> Infer
           ( Map String ([TVar], [(SrcPos, (String, [Type]))])
           , Map String (VariantIx, (String, [TVar]), [Type], Span)
           )
checkTypeDefsNoConflicting =
    flip foldM (builtinDataTypes, builtinConstructors)
        $ \(tds', csAcc) td@(Ast.TypeDef x _ _) -> do
            when (Map.member (idstr x) tds') (throwError (ConflictingTypeDef x))
            (td', cs) <- checkTypeDef td
            case listToMaybe (Map.elems (Map.intersection cs csAcc)) of
                Just (cId, _) -> throwError (ConflictingCtorDef cId)
                Nothing ->
                    pure
                        ( uncurry Map.insert td' tds'
                        , Map.union (fmap snd cs) csAcc
                        )

checkTypeDef
    :: Ast.TypeDef
    -> Infer
           ( (String, ([TVar], [(SrcPos, (String, [Type]))]))
           , Map
                 String
                 (Id Big, (VariantIx, (String, [TVar]), [Type], Span))
           )
checkTypeDef (Ast.TypeDef x' ps (Ast.ConstructorDefs cs)) = do
    let x = idstr x'
    let ps' = map TVExplicit ps
    let cs' = map (\(Id (WithPos p x), ts) -> (p, (x, ts))) cs
    let cSpan = length cs
    cs''' <- foldM
        (\cs'' (i, (cx, cps)) -> if Map.member (idstr cx) cs''
            then throwError (ConflictingCtorDef cx)
            else pure
                (Map.insert (idstr cx) (cx, (i, (x, ps'), cps, cSpan)) cs'')
        )
        Map.empty
        (zip [0 ..] cs)
    pure ((x, (ps', cs')), cs''')

builtinDataTypes :: Map String ([TVar], [(SrcPos, (String, [Type]))])
builtinDataTypes = Map.fromList
    (map (\(x, ps, cs) -> (x, (ps, map (dummyPos, ) cs))) builtinDataTypes')

builtinConstructors :: Map String (VariantIx, (String, [TVar]), [Type], Span)
builtinConstructors = Map.unions (map builtinConstructors' builtinDataTypes')

builtinConstructors'
    :: (String, [TVar], [(String, [Type])])
    -> Map String (VariantIx, (String, [TVar]), [Type], Span)
builtinConstructors' (x, ps, cs) =
    let cSpan = length cs
    in
        foldl'
            (\csAcc (i, (cx, cps)) ->
                Map.insert cx (i, (x, ps), cps, cSpan) csAcc
            )
            Map.empty
            (zip [0 ..] cs)

builtinDataTypes' :: [(String, [TVar], [(String, [Type])])]
builtinDataTypes' =
    [ ( "Array"
      , [TVImplicit 0]
      , [("Array", [TBox (TVar (TVImplicit 0)), TPrim TNat])]
      )
    , ("Str", [], [("Str", [TConst ("Array", [TPrim TNat8])])])
    ]

inferDefs :: [Ast.Def] -> Infer Defs
inferDefs defs = do
    let ordered = orderDefs defs
    inferDefsComponents ordered

-- For unification to work properly with mutually recursive functions,
-- we need to create a dependency graph of non-recursive /
-- directly-recursive functions and groups of mutual functions. We do
-- this by creating a directed acyclic graph (DAG) of strongly
-- connected components (SCC), where a node is a definition and an
-- edge is a reference to another definition. For each SCC, we infer
-- types for all the definitions / the single definition before
-- generalizing.
orderDefs :: [Ast.Def] -> [SCC Ast.Def]
orderDefs = stronglyConnComp . graph
    where graph = map (\d@(n, _) -> (d, n, Set.toList (freeVars d)))

inferDefsComponents :: [SCC Ast.Def] -> Infer Defs
inferDefsComponents = \case
    [] -> pure Map.empty
    (scc : sccs) -> do
        let (idents, rhss) = unzip (flattenSCC scc)
        let (mayscms, bodies) = unzip rhss
        checkUserSchemes (catMaybes mayscms)
        let mayscms' = map (fmap unpos) mayscms
        let names = map idstr idents
        ts <- replicateM (length names) fresh
        let scms = map
                (\(mayscm, t) -> fromMaybe (Forall Set.empty t) mayscm)
                (zip mayscms' ts)
        bodies' <-
            withLocals (zip names scms)
            $ forM (zip bodies scms)
            $ \(body, Forall _ t1) -> do
                (t2, body') <- infer body
                unify (Expected t1) (Found (getPos body) t2)
                pure body'
        generalizeds <- mapM generalize ts
        let scms' = zipWith fromMaybe generalizeds mayscms'
        let annotDefs = Map.fromList (zip names (zip scms' bodies'))
        annotRest <- withLocals (zip names scms') (inferDefsComponents sccs)
        pure (Map.union annotRest annotDefs)

-- | Verify that user-provided type signature schemes are valid
checkUserSchemes :: [WithPos Scheme] -> Infer ()
checkUserSchemes scms = forM_ scms $ \(WithPos p s1@(Forall _ t)) ->
    generalize t
        >>= \s2 -> when (s1 /= s2) (throwError (InvalidUserTypeSig p s1 s2))

infer :: Ast.Expr -> Infer (Type, Expr)
infer (WithPos pos e) = case e of
    Ast.Lit l -> pure (litType l, Lit l)
    Ast.Var (Id (WithPos p "_")) -> throwError (FoundHole p)
    Ast.Var x -> fmap (\t -> (t, Var (TypedVar (idstr x) t))) (lookupEnv x)
    Ast.App f a -> do
        ta <- fresh
        tr <- fresh
        (tf', f') <- infer f
        unify (Expected (TFun ta tr)) (Found (getPos f) tf')
        (ta', a') <- infer a
        unify (Expected ta) (Found (getPos a) ta')
        pure (tr, App f' a' tr)
    Ast.If p c a -> do
        (tp, p') <- infer p
        (tc, c') <- infer c
        (ta, a') <- infer a
        unify (Expected (TPrim TBool)) (Found (getPos p) tp)
        unify (Expected tc) (Found (getPos a) ta)
        pure (tc, If p' c' a')
    Ast.Fun p b -> do
        tp <- fresh
        (tb, b') <- withLocal (idstr p, Forall Set.empty tp) (infer b)
        pure (TFun tp tb, Fun (idstr p, tp) (b', tb))
    Ast.Let defs b -> do
        annotDefs <- inferDefs (fromList1 defs)
        let defsScms = fmap (\(scm, _) -> scm) annotDefs
        (bt, b') <- withLocals' defsScms (infer b)
        pure (bt, Let annotDefs b')
    Ast.TypeAscr x t -> do
        (tx, x') <- infer x
        unify (Expected t) (Found (getPos x) tx)
        pure (t, x')
    Ast.Match matchee cases -> do
        (tmatchee, matchee') <- infer matchee
        (tbody, cases') <- inferCases (Expected tmatchee) cases
        dt <- toDecisionTree' pos tmatchee cases'
        pure (tbody, Match matchee' dt tbody)
    Ast.FunMatch cases -> do
        tpat <- fresh
        (tbody, cases') <- inferCases (Expected tpat) cases
        dt <- toDecisionTree' pos tpat cases'
        pure (TFun tpat tbody, FunMatch dt tpat tbody)
    Ast.Ctor c -> inferExprConstructor c

toDecisionTree' :: SrcPos -> Type -> [(SrcPos, Pat, Expr)] -> Infer DecisionTree
toDecisionTree' pos tpat cases = do
    -- TODO: Could we do this differently, more efficiently?
    --
    -- Match needs to be able to match on the pattern types to generate proper
    -- error messages for inexhaustive patterns, so apply substitutions.
    s <- use substs
    let tpat' = subst s tpat
    let cases' = map (\(pos, p, e) -> (pos, substPat s p, e)) cases
    mTypeDefs <- views envTypeDefs (fmap (map fst . snd))
    lift (lift (toDecisionTree mTypeDefs pos tpat' cases'))

-- | All the patterns must be of the same types, and all the bodies must be of
--   the same type.
inferCases
    :: ExpectedType -- Type of matchee. Expected type of pattern.
    -> NonEmpty (Ast.Pat, Ast.Expr)
    -> Infer (Type, [(SrcPos, Pat, Expr)])
inferCases tmatchee cases = do
    (tpats, tbodies, cases') <- fmap unzip3 (mapM inferCase (fromList1 cases))
    forM_ tpats (unify tmatchee)
    tbody <- fresh
    forM_ tbodies (unify (Expected tbody))
    pure (tbody, cases')

inferCase
    :: (Ast.Pat, Ast.Expr) -> Infer (FoundType, FoundType, (SrcPos, Pat, Expr))
inferCase (p, b) = do
    (tp, p', pvs) <- inferPat p
    let pvs' = Map.mapKeys Ast.idstr pvs
    (tb, b') <- withLocals' pvs' (infer b)
    let ppos = getPos p
    pure (Found ppos tp, Found (getPos b) tb, (ppos, p', b'))

inferPat :: Ast.Pat -> Infer (Type, Pat, Map (Id Small) Scheme)
inferPat = \case
    Ast.PConstruction pos c ps -> inferPatConstruction pos c ps
    Ast.PVar (Id (WithPos _ "_")) -> do
        tv <- fresh
        pure (tv, PWild, Map.empty)
    Ast.PVar x -> do
        tv <- fresh
        let x' = TypedVar (idstr x) tv
        pure (tv, PVar x', Map.singleton x (Forall Set.empty tv))

inferPatConstruction
    :: SrcPos -> Id Big -> [Ast.Pat] -> Infer (Type, Pat, Map (Id Small) Scheme)
inferPatConstruction pos c cArgs = do
    (variantIx, tdefLhs, cParams, cSpan) <- lookupEnvConstructor c
    let arity = length cParams
    let nArgs = length cArgs
    unless (arity == nArgs) (throwError (CtorArityMismatch pos c arity nArgs))
    (tdefInst, cParams') <- instantiateConstructorOfTypeDef tdefLhs cParams
    let t = TConst tdefInst
    (cArgTs, cArgs', cArgsVars) <- fmap unzip3 (mapM inferPat cArgs)
    cArgsVars' <- nonconflictingPatVarDefs cArgsVars
    forM_ (zip3 cParams' cArgTs cArgs) $ \(cParamT, cArgT, cArg) ->
        unify (Expected cParamT) (Found (getPos cArg) cArgT)
    let con = Con { variant = variantIx, span = cSpan, argTs = cArgTs }
    pure (t, PCon con cArgs', cArgsVars')

nonconflictingPatVarDefs
    :: [Map (Id Small) Scheme] -> Infer (Map (Id Small) Scheme)
nonconflictingPatVarDefs = flip foldM Map.empty $ \acc ks ->
    case listToMaybe (Map.keys (Map.intersection acc ks)) of
        Just (Id (WithPos pos v)) -> throwError (ConflictingPatVarDefs pos v)
        Nothing -> pure (Map.union acc ks)

inferExprConstructor :: Id Big -> Infer (Type, Expr)
inferExprConstructor c = do
    (variantIx, tdefLhs, cParams, _) <- lookupEnvConstructor c
    (tdefInst, cParams') <- instantiateConstructorOfTypeDef tdefLhs cParams
    let t = foldr TFun (TConst tdefInst) cParams'
    pure (t, Ctor variantIx tdefInst cParams')

instantiateConstructorOfTypeDef
    :: (String, [TVar]) -> [Type] -> Infer (TConst, [Type])
instantiateConstructorOfTypeDef (tName, tParams) cParams = do
    tVars <- mapM (const fresh) tParams
    let cParams' = map (subst (Map.fromList (zip tParams tVars))) cParams
    pure ((tName, tVars), cParams')

lookupEnvConstructor
    :: Id Big -> Infer (VariantIx, (String, [TVar]), [Type], Span)
lookupEnvConstructor (Id (WithPos pos cx)) =
    views envCtors (Map.lookup cx)
        >>= maybe (throwError (UndefCtor pos cx)) pure

litType :: Const -> Type
litType = \case
    Unit -> TPrim TUnit
    Int _ -> TPrim TInt
    Double _ -> TPrim TDouble
    Char _ -> TPrim TChar
    Str _ -> TConst ("Str", [])
    Bool _ -> TPrim TBool

lookupEnv :: Id Small -> Infer Type
lookupEnv (Id (WithPos pos x)) = views envDefs (Map.lookup x) >>= \case
    Just scm -> instantiate scm
    Nothing -> throwError (UndefVar pos x)

-- Unification
--------------------------------------------------------------------------------
newtype ExpectedType = Expected Type
data FoundType = Found SrcPos Type

unify :: ExpectedType -> FoundType -> Infer ()
unify (Expected t1) (Found pos t2) = do
    s1 <- use substs
    s2 <- unify' (Expected (subst s1 t1)) (Found pos (subst s1 t2))
    assign substs (composeSubsts s2 s1)

unify' :: ExpectedType -> FoundType -> Infer Subst
unify' (Expected t1) (Found pos t2) = lift $ lift $ withExcept
    (\case
        InfiniteType'' a t -> InfType pos t1 t2 a t
        UnificationFailed'' t'1 t'2 -> UnificationFailed pos t1 t2 t'1 t'2
    )
    (unify'' t1 t2)

data UnifyErr'' = InfiniteType'' TVar Type | UnificationFailed'' Type Type

unify'' :: Type -> Type -> Except UnifyErr'' Subst
unify'' = curry $ \case
    (TPrim a, TPrim b) | a == b -> pure Map.empty
    (TConst (c0, ts0), TConst (c1, ts1)) | c0 == c1 ->
        if length ts0 /= length ts1
            then ice "lengths of TConst params differ in unify"
            else unifys ts0 ts1
    (TVar a, TVar b) | a == b -> pure Map.empty
    (TVar a, t) | occursIn a t -> throwError (InfiniteType'' a t)
    -- Do not allow "override" of explicit (user given) type variables.
    (a@(TVar (TVExplicit _)), b@(TVar (TVImplicit _))) -> unify'' b a
    (a@(TVar (TVExplicit _)), b) -> throwError (UnificationFailed'' a b)
    (TVar a, t) -> pure (Map.singleton a t)
    (t, TVar a) -> unify'' (TVar a) t
    (TFun t1 t2, TFun u1 u2) -> unifys [t1, t2] [u1, u2]
    (t1, t2) -> throwError (UnificationFailed'' t1 t2)

unifys :: [Type] -> [Type] -> Except UnifyErr'' Subst
unifys ts us = foldM
    (\s (t, u) -> fmap (flip composeSubsts s) (unify'' (subst s t) (subst s u)))
    Map.empty
    (zip ts us)

occursIn :: TVar -> Type -> Bool
occursIn a t = Set.member a (ftv t)

-- Instantiation and generalization
--------------------------------------------------------------------------------
instantiate :: Scheme -> Infer Type
instantiate (Forall params t) = do
    let params' = Set.toList params
    args <- mapM (const fresh) params'
    pure (subst (Map.fromList (zip params' args)) t)

generalize :: Type -> Infer Scheme
generalize t = do
    env <- ask
    s <- use substs
    let t' = subst s t
    pure (Forall (generalize' (substEnv s env) t') t')

generalize' :: Env -> Type -> Set TVar
generalize' env t = Set.difference (ftv t) (ftvEnv env)

substEnv :: Subst -> Env -> Env
substEnv s = over (envDefs . mapped . scmBody) (subst s)

-- Free type variables
--------------------------------------------------------------------------------
ftv :: Type -> Set TVar
ftv = \case
    TVar tv -> Set.singleton tv
    TPrim _ -> Set.empty
    TFun t1 t2 -> Set.union (ftv t1) (ftv t2)
    TBox t -> ftv t
    TConst (_, ts) -> Set.unions (map ftv ts)

ftvEnv :: Env -> Set TVar
ftvEnv = Set.unions . map (ftvScheme . snd) . Map.toList . view envDefs

ftvScheme :: Scheme -> Set TVar
ftvScheme (Forall tvs t) = Set.difference (ftv t) tvs
