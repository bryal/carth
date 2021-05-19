{-# LANGUAGE TemplateHaskell, DataKinds, RankNTypes #-}

module Infer (inferTopDefs, checkType', checkType'') where

import Prelude hiding (span)
import Lens.Micro.Platform (makeLenses, over, view, mapped, to, Lens')
import Control.Applicative hiding (Const(..))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Writer
import Data.Bifunctor
import Data.Functor
import Data.Graph (SCC(..), stronglyConnComp)
import Data.List hiding (span)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Arrow ((>>>))

import Misc
import SrcPos
import FreeVars
import Subst
import qualified Parsed
import Parsed (Id(..), IdCase(..), idstr, defLhs)
import Err
import Inferred hiding (Id)
import TypeAst hiding (TConst)


newtype ExpectedType = Expected Type
data FoundType = Found SrcPos Type

type Constraint = (ExpectedType, FoundType)

data Env = Env
    { _envTypeDefs :: TypeDefs
    -- Separarate global (and virtual) defs and local defs, because `generalize` only has
    -- to look at local defs.
    , _envVirtuals :: Map String Scheme
    , _envGlobDefs :: Map String Scheme
    , _envLocalDefs :: Map String Scheme
    -- | Maps a constructor to its variant index in the type definition it
    --   constructs, the signature/left-hand-side of the type definition, the
    --   types of its parameters, and the span (number of constructors) of the
    --   datatype
    , _envCtors :: Map String (VariantIx, (String, [TVar]), [Type], Span)
    }
makeLenses ''Env

type FreshTVs = [String]

type Infer a = WriterT [Constraint] (ReaderT Env (StateT FreshTVs (Except TypeErr))) a

------------------------------------------------------------------------------------------
-- Inference
------------------------------------------------------------------------------------------

inferTopDefs :: TypeDefs -> Ctors -> Externs -> [Parsed.Def] -> Except TypeErr Defs
inferTopDefs tdefs ctors externs defs =
    let initEnv = Env { _envTypeDefs = tdefs
                      , _envVirtuals = builtinVirtuals
                      , _envGlobDefs = fmap (Forall Set.empty . fst) externs
                      , _envLocalDefs = Map.empty
                      , _envCtors = ctors
                      }
        freshTvs =
            let ls = "abcdehjkpqrstuvxyz"
                ns = map show [1 :: Word .. 99]
                vs = [ l : n | l <- ls, n <- ns ] ++ [ l : v | l <- ls, v <- vs ]
            in  vs
    in  evalStateT
            (runReaderT (fmap fst (runWriterT (inferDefs envGlobDefs defs))) initEnv)
            freshTvs
  where
    builtinVirtuals :: Map String Scheme
    builtinVirtuals =
        let tv a = TVExplicit (Parsed.Id (WithPos (SrcPos "<builtin>" 0 0 Nothing) a))
            tva = tv "a"
            ta = TVar tva
            tvb = tv "b"
            tb = TVar tvb
            arithScm = Forall (Set.fromList [tva]) (tfun ta (tfun ta ta))
            bitwiseScm = arithScm
            relScm = Forall (Set.fromList [tva]) (tfun ta (tfun ta tBool))
        in  Map.fromList
                $ [ ("+", arithScm)
                  , ("-", arithScm)
                  , ("*", arithScm)
                  , ("/", arithScm)
                  , ("rem", arithScm)
                  , ("shift-l", bitwiseScm)
                  , ("shift-r", bitwiseScm)
                  , ("ashift-r", bitwiseScm)
                  , ("bit-and", bitwiseScm)
                  , ("bit-or", bitwiseScm)
                  , ("bit-xor", bitwiseScm)
                  , ("=", relScm)
                  , ("/=", relScm)
                  , (">", relScm)
                  , (">=", relScm)
                  , ("<", relScm)
                  , ("<=", relScm)
                  , ("transmute", Forall (Set.fromList [tva, tvb]) (TFun ta tb))
                  , ("deref", Forall (Set.fromList [tva]) (TFun (TBox ta) ta))
                  , ( "store"
                    , Forall (Set.fromList [tva]) (TFun ta (TFun (TBox ta) (TBox ta)))
                    )
                  , ("cast", Forall (Set.fromList [tva, tvb]) (TFun ta tb))
                  ]

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
    checkNoDuplicateDefs Set.empty defs
    let ordered = orderDefs defs
    foldr
        (\scc inferRest -> do
            def <- inferComponent scc
            Topo rest <- augment envDefs (Map.fromList (defSigs def)) inferRest
            pure (Topo (def : rest))
        )
        (pure (Topo []))
        ordered
  where
    checkNoDuplicateDefs :: Set String -> [Parsed.Def] -> Infer ()
    checkNoDuplicateDefs already = uncons >>> fmap (first defLhs) >>> \case
        Just (Id (WithPos p x), ds) -> if Set.member x already
            then throwError (ConflictingVarDef p x)
            else checkNoDuplicateDefs (Set.insert x already) ds
        Nothing -> pure ()

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
    where graph = map (\d -> (d, defLhs d, Set.toList (freeVars d)))

inferComponent :: SCC Parsed.Def -> Infer Def
inferComponent = \case
    AcyclicSCC vert -> fmap VarDef (inferNonrecDef vert)
    CyclicSCC verts -> fmap RecDefs (inferRecDefs verts)

inferNonrecDef :: Parsed.Def -> Infer VarDef
inferRecDefs :: [Parsed.Def] -> Infer RecDefs
(inferNonrecDef, inferRecDefs) = (inferNonrecDef', inferRecDefs')
  where
    inferNonrecDef' (Parsed.FunDef dpos lhs mayscm params body) =
        -- FIXME: Just wanted to get things working, but this isn't really better than
        --        doing the fold in the parser. Handle this such that we don't have to
        --        assign the definition position to the nested lambdas.
        inferNonrecDef' $ Parsed.VarDef dpos lhs mayscm $ foldr
            (\p b -> WithPos dpos (Parsed.FunMatch [(p, b)]))
            body
            params
    inferNonrecDef' (Parsed.VarDef dpos lhs mayscm body) = do
        t <- fresh
        (body', cs) <- listen $ inferDef t lhs mayscm (getPos body) (infer body)
        sub <- lift $ lift $ lift $ solve cs
        env <- view envLocalDefs
        let scm = generalize (substEnv sub env) (subst sub t)
        let body'' = substExpr sub body'
        pure (idstr lhs, WithPos dpos (scm, body''))

    inferRecDefs' ds = do
        ts <- replicateM (length ds) fresh
        let (names, poss) = unzip $ flip map ds $ \case
                Parsed.FunDef p x _ _ _ -> (idstr x, p)
                Parsed.VarDef p x _ _ -> (idstr x, p)
        let dummyDefs = Map.fromList (zip names (map (Forall Set.empty) ts))
        (fs, cs) <- listen $ augment envLocalDefs dummyDefs $ zipWithM inferRecDef ts ds
        sub <- lift $ lift $ lift $ solve cs
        env <- view envLocalDefs
        let scms = map (generalize (substEnv sub env) . subst sub) ts
        let fs' = map (mapPosd (substFunMatch sub)) fs
        pure (zip names (zipWith3 (curry . WithPos) poss scms fs'))

    inferRecDef :: Type -> Parsed.Def -> Infer (WithPos FunMatch)
    inferRecDef t = \case
        Parsed.FunDef fpos lhs mayscm params body ->
            let (initps, lastp) = fromJust $ unsnoc params
            in  fmap (WithPos fpos) $ inferDef t lhs mayscm fpos $ inferFunMatch $ foldr
                    (\p cs -> [(p, WithPos fpos (Parsed.FunMatch cs))])
                    [(lastp, body)]
                    initps
        Parsed.VarDef fpos lhs mayscm (WithPos _ (Parsed.FunMatch cs)) ->
            fmap (WithPos fpos) $ inferDef t lhs mayscm fpos (inferFunMatch cs)
        Parsed.VarDef _ (Id lhs) _ _ -> throwError (RecursiveVarDef lhs)

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
            if (s1 == s2)
                then pure (Just s1)
                else throwError (InvalidUserTypeSig pos s1 s2)

infer :: Parsed.Expr -> Infer (Type, Expr)
infer (WithPos pos e) = fmap (second (WithPos pos)) $ case e of
    Parsed.Lit l -> pure (litType l, Lit l)
    Parsed.Var (Id (WithPos p "_")) -> throwError (FoundHole p)
    Parsed.Var x -> fmap (\(t, tv) -> (t, Var tv)) (lookupVar x)
    Parsed.App f a -> do
        ta <- fresh
        tr <- fresh
        (tf', f') <- infer f
        (ta', a') <- infer a
        unify (Expected (TFun ta tr)) (Found (getPos f) tf')
        unify (Expected ta) (Found (getPos a) ta')
        pure (tr, App f' a' tr)
    Parsed.If p c a -> do
        (tp, p') <- infer p
        (tc, c') <- infer c
        (ta, a') <- infer a
        unify (Expected tBool) (Found (getPos p) tp)
        unify (Expected tc) (Found (getPos a) ta)
        pure (tc, If p' c' a')
    Parsed.Let1 def body -> inferLet1 pos def body
    Parsed.Let defs body ->
        -- FIXME: positions
        let (def, defs') = fromJust $ uncons defs
        in  inferLet1 pos def $ foldr (\d b -> WithPos pos (Parsed.Let1 d b)) body defs'
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
    Parsed.Match matchee cases -> inferMatch pos matchee cases
    Parsed.FunMatch cases -> fmap (second FunMatch) (inferFunMatch cases)
    Parsed.Ctor c -> do
        (variantIx, tdefLhs, cParams, cSpan) <- lookupEnvConstructor c
        (tdefInst, cParams') <- instantiateConstructorOfTypeDef tdefLhs cParams
        let t = foldr TFun (TConst tdefInst) cParams'
        pure (t, Ctor variantIx cSpan tdefInst cParams')
    Parsed.Sizeof t -> fmap ((TPrim TNatSize, ) . Sizeof) (checkType pos t)

inferLet1 :: SrcPos -> Parsed.DefLike -> Parsed.Expr -> Infer (Type, Expr')
inferLet1 pos defl body = case defl of
    Parsed.Def def -> do
        def' <- inferNonrecDef def
        (t, body') <- augment1 envLocalDefs (defSig def') (infer body)
        pure (t, Let (VarDef def') body')
    Parsed.Deconstr pat matchee -> inferMatch pos matchee [(pat, body)]

inferMatch :: SrcPos -> Parsed.Expr -> [(Parsed.Pat, Parsed.Expr)] -> Infer (Type, Expr')
inferMatch pos matchee cases = do
    (tmatchee, matchee') <- infer matchee
    (tbody, cases') <- inferCases (Expected tmatchee) cases
    let f = WithPos pos (FunMatch (cases', tmatchee, tbody))
    pure (tbody, App f matchee' tbody)

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
  where
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
            in  pure (tStr, p, Map.empty)
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

    nonconflictingPatVarDefs = flip foldM Map.empty $ \acc ks ->
        case listToMaybe (Map.keys (Map.intersection acc ks)) of
            Just (Id (WithPos pos v)) -> throwError (ConflictingPatVarDefs pos v)
            Nothing -> pure (Map.union acc ks)

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
    Str _ -> tStr

lookupVar :: Id 'Small -> Infer (Type, Var)
lookupVar (Id x'@(WithPos pos x)) = do
    virt <- fmap (Map.lookup x) (view envVirtuals)
    glob <- fmap (Map.lookup x) (view envGlobDefs)
    local <- fmap (Map.lookup x) (view envLocalDefs)
    case fmap (NonVirt, ) (local <|> glob) <|> fmap (Virt, ) virt of
        Just (virt, scm) -> instantiate scm <&> \t -> (t, (virt, TypedVar x' t))
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
fresh' = fmap TVImplicit (gets head <* modify tail)

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
