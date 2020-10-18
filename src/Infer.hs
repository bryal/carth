{-# LANGUAGE LambdaCase, TemplateHaskell, DataKinds, FlexibleContexts, TupleSections
           , RankNTypes #-}

module Infer (inferTopDefs, checkType', checkType'') where

import Prelude hiding (span)
import Lens.Micro.Platform (makeLenses, over, view, mapped, to, Lens')
import Control.Applicative hiding (Const(..))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Writer
import Data.Bifunctor
import Data.Graph (SCC(..), stronglyConnComp)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import qualified Data.Set as Set
import Control.Arrow ((>>>))

import Misc
import SrcPos
import FreeVars
import Subst
import qualified Parsed
import Parsed (Id(..), IdCase(..), idstr)
import Err
import Inferred hiding (Id)
import TypeAst hiding (TConst)


newtype ExpectedType = Expected Type
data FoundType = Found SrcPos Type

type Constraint = (ExpectedType, FoundType)

data Env = Env
    { _envTypeDefs :: TypeDefs
    -- Separarate global defs and local defs, because `generalize` only has to look at
    -- local defs.
    , _envGlobDefs :: Map String Scheme
    , _envLocalDefs :: Map String Scheme
    -- | Maps a constructor to its variant index in the type definition it
    --   constructs, the signature/left-hand-side of the type definition, the
    --   types of its parameters, and the span (number of constructors) of the
    --   datatype
    , _envCtors :: Map String (VariantIx, (String, [TVar]), [Type], Span)
    }
makeLenses ''Env

type TVCount = Word

type Infer a = WriterT [Constraint] (ReaderT Env (StateT TVCount (Except TypeErr))) a

------------------------------------------------------------------------------------------
-- Inference
------------------------------------------------------------------------------------------

inferTopDefs :: TypeDefs -> Ctors -> Externs -> [Parsed.Def] -> Except TypeErr Defs
inferTopDefs tdefs ctors externs defs =
    let initEnv = Env
            { _envTypeDefs = tdefs
            , _envGlobDefs = Map.union (fmap (Forall Set.empty . fst) externs)
                                       builtinVirtuals
            , _envLocalDefs = Map.empty
            , _envCtors = ctors
            }
    in  evalStateT
            (runReaderT (fmap fst (runWriterT (inferDefs envGlobDefs defs))) initEnv)
            0

checkType :: SrcPos -> Parsed.Type -> Infer Type
checkType pos t = view envTypeDefs >>= \tds -> checkType' tds pos t

checkType' :: MonadError TypeErr m => TypeDefs -> SrcPos -> Parsed.Type -> m Type
checkType' tdefs = checkType'' (\x -> fmap (length . fst) (Map.lookup x tdefs))

checkType''
    :: MonadError TypeErr m => (String -> Maybe Int) -> SrcPos -> Parsed.Type -> m Type
checkType'' tdefsParams pos = go
  where
    go = \case
        Parsed.TVar v -> pure (TVar v)
        Parsed.TPrim p -> pure (TPrim p)
        Parsed.TConst tc -> fmap TConst (checkTConst tc)
        Parsed.TFun f a -> liftA2 TFun (go f) (go a)
        Parsed.TBox t -> fmap TBox (go t)
    checkTConst (x, inst) = case tdefsParams x of
        Just expectedN -> do
            let foundN = length inst
            if (expectedN == foundN)
                then do
                    inst' <- mapM go inst
                    pure (x, inst')
                else throwError (TypeInstArityMismatch pos x expectedN foundN)
        Nothing -> throwError (UndefType pos x)

inferDefs :: Lens' Env (Map String Scheme) -> [Parsed.Def] -> Infer Defs
inferDefs envDefs defs = do
    checkNoDuplicateDefs defs
    let ordered = orderDefs defs
    foldr
        (\scc inferRest -> do
            def <- inferComponent scc
            Topo rest <- augment envDefs (Map.fromList (defSigs def)) inferRest
            pure (Topo (def : rest))
        )
        (pure (Topo []))
        ordered

checkNoDuplicateDefs :: [Parsed.Def] -> Infer ()
checkNoDuplicateDefs = checkNoDuplicateDefs' Set.empty
  where
    checkNoDuplicateDefs' already = \case
        (Id (WithPos p x), _) : ds -> if Set.member x already
            then throwError (ConflictingVarDef p x)
            else checkNoDuplicateDefs' (Set.insert x already) ds
        [] -> pure ()

-- For unification to work properly with mutually recursive functions,
-- we need to create a dependency graph of non-recursive /
-- directly-recursive functions and groups of mutual functions. We do
-- this by creating a directed acyclic graph (DAG) of strongly
-- connected components (SCC), where a node is a definition and an
-- edge is a reference to another definition. For each SCC, we infer
-- types for all the definitions / the single definition before
-- generalizing.
orderDefs :: [Parsed.Def] -> [SCC Parsed.Def]
orderDefs = stronglyConnComp . graph
    where graph = map (\d@(n, _) -> (d, n, Set.toList (freeVars d)))

inferComponent :: SCC Parsed.Def -> Infer Def
inferComponent = \case
    AcyclicSCC vert -> fmap VarDef (inferVarDef vert)
    CyclicSCC verts -> fmap RecDefs (inferRecDefs verts)

inferVarDef :: Parsed.Def -> Infer VarDef
inferRecDefs :: [Parsed.Def] -> Infer RecDefs
(inferVarDef, inferRecDefs) = (inferVarDef', inferRecDefs')
  where
    inferVarDef' (lhs, WithPos defPos (mayscm, body)) = do
        t <- fresh
        (body', cs) <- listen $ inferDef t lhs mayscm (getPos body) (infer body)
        sub <- lift $ lift $ lift $ solve cs
        env <- view envLocalDefs
        let scm = generalize (substEnv sub env) (subst sub t)
        let body'' = substExpr sub body'
        pure (idstr lhs, WithPos defPos (scm, body''))

    inferRecDefs' ds = do
        ts <- replicateM (length ds) fresh
        let (names, poss) = unzip (map (bimap idstr getPos) ds)
        let dummyDefs = Map.fromList (zip names (map (Forall Set.empty) ts))
        (fs, cs) <- listen $ augment envLocalDefs dummyDefs $ zipWithM inferRecDef ts ds
        sub <- lift $ lift $ lift $ solve cs
        env <- view envLocalDefs
        let scms = map (generalize (substEnv sub env) . subst sub) ts
        let fs' = map (mapPosd (substFunMatch sub)) fs
        pure (zip names (zipWith3 (curry . WithPos) poss scms fs'))

    inferRecDef :: Type -> Parsed.Def -> Infer (WithPos FunMatch)
    inferRecDef t = uncurry $ \(Id lhs) -> unpos >>> \case
        (mayscm, WithPos fPos (Parsed.FunMatch cs)) ->
            fmap (WithPos fPos) $ inferDef t (Id lhs) mayscm fPos (inferFunMatch cs)
        _ -> throwError (RecursiveVarDef lhs)

    inferDef t lhs mayscm bodyPos inferBody = do
        checkScheme (idstr lhs) mayscm >>= \case
            Just (Forall _ scmt) -> unify (Expected scmt) (Found bodyPos t)
            Nothing -> pure ()
        (t', body') <- inferBody
        unify (Expected t) (Found bodyPos t')
        pure body'

-- | Verify that user-provided type signature schemes are valid
checkScheme :: String -> Maybe Parsed.Scheme -> Infer (Maybe Scheme)
checkScheme = curry $ \case
    ("main", Nothing) -> pure (Just (Forall Set.empty mainType))
    ("main", Just s@(Parsed.Forall pos vs t)) | Set.size vs /= 0 || t /= mainType ->
        throwError (WrongMainType pos s)
    (_, Nothing) -> pure Nothing
    (_, Just (Parsed.Forall pos vs t)) -> do
        t' <- checkType pos t
        let s1 = Forall vs t'
        env <- view envLocalDefs
        let s2 = generalize env t'
        if (s1 == s2) then pure (Just s1) else throwError (InvalidUserTypeSig pos s1 s2)

infer :: Parsed.Expr -> Infer (Type, Expr)
infer (WithPos pos e) = fmap (second (WithPos pos)) $ case e of
    Parsed.Lit l -> pure (litType l, Lit l)
    Parsed.Var (Id (WithPos p "_")) -> throwError (FoundHole p)
    Parsed.Var x@(Id x') -> fmap (\t -> (t, Var (TypedVar x' t))) (lookupEnv x)
    Parsed.App f a -> do
        ta <- fresh
        tr <- fresh
        (tf', f') <- infer f
        unify (Expected (TFun ta tr)) (Found (getPos f) tf')
        (ta', a') <- infer a
        unify (Expected ta) (Found (getPos a) ta')
        pure (tr, App f' a' tr)
    Parsed.If p c a -> do
        (tp, p') <- infer p
        (tc, c') <- infer c
        (ta, a') <- infer a
        unify (Expected tBool) (Found (getPos p) tp)
        unify (Expected tc) (Found (getPos a) ta)
        pure (tc, If p' c' a')
    Parsed.Let1 def body -> do
        def' <- inferVarDef def
        (t, body') <- augment1 envLocalDefs (defSig def') (infer body)
        pure (t, Let (VarDef def') body')
    Parsed.LetRec defs b -> do
        Topo defs' <- inferDefs envLocalDefs defs
        let withDef def inferX = do
                (tx, x') <- withLocals (defSigs def) inferX
                pure (tx, WithPos pos (Let def x'))
        fmap (second unpos) (foldr withDef (infer b) defs')
    Parsed.TypeAscr x t -> do
        (tx, WithPos _ x') <- infer x
        t' <- checkType pos t
        unify (Expected t') (Found (getPos x) tx)
        pure (t', x')
    Parsed.Match matchee cases -> do
        (tmatchee, matchee') <- infer matchee
        (tbody, cases') <- inferCases (Expected tmatchee) cases
        let f = WithPos pos (FunMatch (cases', tmatchee, tbody))
        pure (tbody, App f matchee' tbody)
    Parsed.FunMatch cases -> fmap (second FunMatch) (inferFunMatch cases)
    Parsed.Ctor c -> inferExprConstructor c
    Parsed.Sizeof t -> fmap ((TPrim TNatSize, ) . Sizeof) (checkType pos t)

inferFunMatch :: [(Parsed.Pat, Parsed.Expr)] -> Infer (Type, FunMatch)
inferFunMatch cases = do
    tpat <- fresh
    (tbody, cases') <- inferCases (Expected tpat) cases
    pure (TFun tpat tbody, (cases', tpat, tbody))

-- | All the patterns must be of the same types, and all the bodies must be of
--   the same type.
inferCases
    :: ExpectedType -- Type of matchee. Expected type of pattern.
    -> [(Parsed.Pat, Parsed.Expr)]
    -> Infer (Type, Cases)
inferCases tmatchee cases = do
    (tpats, tbodies, cases') <- fmap unzip3 (mapM inferCase cases)
    forM_ tpats (unify tmatchee)
    tbody <- fresh
    forM_ tbodies (unify (Expected tbody))
    pure (tbody, cases')

inferCase :: (Parsed.Pat, Parsed.Expr) -> Infer (FoundType, FoundType, (Pat, Expr))
inferCase (p, b) = do
    (tp, p', pvs) <- inferPat p
    let pvs' = map (bimap (Parsed.idstr) (Forall Set.empty . TVar)) (Map.toList pvs)
    (tb, b') <- withLocals pvs' (infer b)
    pure (Found (getPos p) tp, Found (getPos b) tb, (p', b'))

-- | Returns the type of the pattern; the pattern in the Pat format that the
--   Match module wants, and a Map from the variables bound in the pattern to
--   fresh schemes.
inferPat :: Parsed.Pat -> Infer (Type, Pat, Map (Id 'Small) TVar)
inferPat pat = fmap (\(t, p, ss) -> (t, WithPos (getPos pat) p, ss)) (inferPat' pat)
  where
    inferPat' = \case
        Parsed.PConstruction pos c ps -> inferPatConstruction pos c ps
        Parsed.PInt _ n -> pure (TPrim TIntSize, intToPCon n 64, Map.empty)
        Parsed.PStr _ s ->
            let span' = ice "span of Con with VariantStr"
                p = PCon (Con (VariantStr s) span' []) []
            in  pure (typeStr, p, Map.empty)
        Parsed.PVar (Id (WithPos _ "_")) -> do
            tv <- fresh
            pure (tv, PWild, Map.empty)
        Parsed.PVar x@(Id x') -> do
            tv <- fresh'
            pure (TVar tv, PVar (TypedVar x' (TVar tv)), Map.singleton x tv)
        Parsed.PBox _ p -> do
            (tp', p', vs) <- inferPat p
            pure (TBox tp', PBox p', vs)
    intToPCon n w = PCon
        (Con { variant = VariantIx (fromIntegral n)
             , span = 2 ^ (w :: Integer)
             , argTs = []
             }
        )
        []

inferPatConstruction
    :: SrcPos -> Id 'Big -> [Parsed.Pat] -> Infer (Type, Pat', Map (Id 'Small) TVar)
inferPatConstruction pos c cArgs = do
    (variantIx, tdefLhs, cParams, cSpan) <- lookupEnvConstructor c
    let arity = length cParams
    let nArgs = length cArgs
    unless (arity == nArgs) (throwError (CtorArityMismatch pos (idstr c) arity nArgs))
    (tdefInst, cParams') <- instantiateConstructorOfTypeDef tdefLhs cParams
    let t = TConst tdefInst
    (cArgTs, cArgs', cArgsVars) <- fmap unzip3 (mapM inferPat cArgs)
    cArgsVars' <- nonconflictingPatVarDefs cArgsVars
    forM_ (zip3 cParams' cArgTs cArgs) $ \(cParamT, cArgT, cArg) ->
        unify (Expected cParamT) (Found (getPos cArg) cArgT)
    let con = Con { variant = VariantIx variantIx, span = cSpan, argTs = cArgTs }
    pure (t, PCon con cArgs', cArgsVars')

nonconflictingPatVarDefs :: [Map (Id 'Small) TVar] -> Infer (Map (Id 'Small) TVar)
nonconflictingPatVarDefs = flip foldM Map.empty $ \acc ks ->
    case listToMaybe (Map.keys (Map.intersection acc ks)) of
        Just (Id (WithPos pos v)) -> throwError (ConflictingPatVarDefs pos v)
        Nothing -> pure (Map.union acc ks)

inferExprConstructor :: Id 'Big -> Infer (Type, Expr')
inferExprConstructor c = do
    (variantIx, tdefLhs, cParams, cSpan) <- lookupEnvConstructor c
    (tdefInst, cParams') <- instantiateConstructorOfTypeDef tdefLhs cParams
    let t = foldr TFun (TConst tdefInst) cParams'
    pure (t, Ctor variantIx cSpan tdefInst cParams')

instantiateConstructorOfTypeDef :: (String, [TVar]) -> [Type] -> Infer (TConst, [Type])
instantiateConstructorOfTypeDef (tName, tParams) cParams = do
    tVars <- mapM (const fresh) tParams
    let cParams' = map (subst (Map.fromList (zip tParams tVars))) cParams
    pure ((tName, tVars), cParams')

lookupEnvConstructor :: Id 'Big -> Infer (VariantIx, (String, [TVar]), [Type], Span)
lookupEnvConstructor (Id (WithPos pos cx)) =
    view (envCtors . to (Map.lookup cx)) >>= maybe (throwError (UndefCtor pos cx)) pure

litType :: Const -> Type
litType = \case
    Int _ -> TPrim TIntSize
    F64 _ -> TPrim TF64
    Str _ -> typeStr

typeStr :: Type
typeStr = TConst ("Str", [])

lookupEnv :: Id 'Small -> Infer Type
lookupEnv (Id (WithPos pos x)) = do
    eg <- view envGlobDefs
    el <- view envLocalDefs
    case (Map.lookup x el <|> Map.lookup x eg) of
        Just scm -> instantiate scm
        Nothing -> throwError (UndefVar pos x)

withLocals :: [(String, Scheme)] -> Infer a -> Infer a
withLocals = augment envLocalDefs . Map.fromList

instantiate :: Scheme -> Infer Type
instantiate (Forall params t) = do
    let params' = Set.toList params
    args <- mapM (const fresh) params'
    pure (subst (Map.fromList (zip params' args)) t)

generalize :: Map String Scheme -> Type -> Scheme
generalize env t = Forall (Set.difference (ftv t) (ftvEnv env)) t
  where
    ftvEnv env = Set.unions (map ftvScheme (Map.elems env))
    ftvScheme (Forall tvs t) = Set.difference (ftv t) tvs

substEnv :: Subst -> Map String Scheme -> Map String Scheme
substEnv s = over (mapped . scmBody) (subst s)

fresh :: Infer Type
fresh = fmap TVar fresh'

fresh' :: Infer TVar
fresh' = fmap TVImplicit (get <* modify (+ 1))

unify :: ExpectedType -> FoundType -> Infer ()
unify e f = tell [(e, f)]

------------------------------------------------------------------------------------------
-- Constraint solver
------------------------------------------------------------------------------------------

data UnifyErr = UInfType TVar Type | UFailed Type Type

solve :: [Constraint] -> Except TypeErr Subst
solve = solve' Map.empty
  where
    solve' :: Subst -> [Constraint] -> Except TypeErr Subst
    solve' sub1 = \case
        [] -> pure sub1
        (Expected et, Found pos ft) : cs -> do
            sub2 <- withExcept (toTypeErr pos et ft) (unifies et ft)
            solve' (composeSubsts sub2 sub1) (map (substConstraint sub2) cs)

    substConstraint sub (Expected t1, Found pos t2) =
        (Expected (subst sub t1), Found pos (subst sub t2))

toTypeErr :: SrcPos -> Type -> Type -> UnifyErr -> TypeErr
toTypeErr pos t1 t2 = \case
    UInfType a t -> InfType pos t1 t2 a t
    UFailed t'1 t'2 -> UnificationFailed pos t1 t2 t'1 t'2

unifies :: Type -> Type -> Except UnifyErr Subst
unifies = curry $ \case
    (TPrim a, TPrim b) | a == b -> pure Map.empty
    (TConst (c0, ts0), TConst (c1, ts1)) | c0 == c1 -> if length ts0 /= length ts1
        then ice "lengths of TConst params differ in unify"
        else unifiesMany ts0 ts1
    (TVar a, TVar b) | a == b -> pure Map.empty
    (TVar a, t) | occursIn a t -> throwError (UInfType a t)
    -- Do not allow "override" of explicit (user given) type variables.
    (a@(TVar (TVExplicit _)), b@(TVar (TVImplicit _))) -> unifies b a
    (a@(TVar (TVExplicit _)), b) -> throwError (UFailed a b)
    (TVar a, t) -> pure (Map.singleton a t)
    (t, TVar a) -> unifies (TVar a) t
    (TFun t1 t2, TFun u1 u2) -> unifiesMany [t1, t2] [u1, u2]
    (TBox t, TBox u) -> unifies t u
    (t1, t2) -> throwError (UFailed t1 t2)

unifiesMany :: [Type] -> [Type] -> Except UnifyErr Subst
unifiesMany ts us = foldM
    (\s (t, u) -> fmap (flip composeSubsts s) (unifies (subst s t) (subst s u)))
    Map.empty
    (zip ts us)

occursIn :: TVar -> Type -> Bool
occursIn a t = Set.member a (ftv t)
