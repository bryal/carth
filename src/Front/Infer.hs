{-# LANGUAGE TemplateHaskell, DataKinds, RankNTypes #-}

module Front.Infer (inferTopDefs, checkType', checkType'') where

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
import Sizeof
import Front.SrcPos
import FreeVars
import Front.Subst
import qualified Front.Parsed as Parsed
import Front.Parsed (Id(..), IdCase(..), idstr, defLhs)
import Front.Err
import Front.Inferred hiding (Id)
import Front.TypeAst hiding (TConst)


newtype ExpectedType = Expected Type
data FoundType = Found SrcPos Type

type EqConstraint = (ExpectedType, FoundType)
type Constraints = ([EqConstraint], [(SrcPos, ClassConstraint)])

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

type Infer a = WriterT Constraints (ReaderT Env (StateT FreshTVs (Except TypeErr))) a

------------------------------------------------------------------------------------------
-- Inference
------------------------------------------------------------------------------------------

inferTopDefs :: TypeDefs -> Ctors -> Externs -> [Parsed.Def] -> Except TypeErr Defs
inferTopDefs tdefs ctors externs defs =
    let initEnv = Env { _envTypeDefs = tdefs
                      , _envVirtuals = builtinVirtuals
                      , _envGlobDefs = fmap (Forall Set.empty Set.empty) externs
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
        let
            tv a = TVExplicit (Parsed.Id (WithPos (SrcPos "<builtin>" 0 0 Nothing) a))
            tva = tv "a"
            ta = TVar tva
            tvb = tv "b"
            tb = TVar tvb
            arithScm = Forall (Set.fromList [tva])
                              (Set.singleton ("Num", [ta]))
                              (tfun [ta, ta] ta)
            bitwiseScm = Forall (Set.fromList [tva])
                                (Set.singleton ("Bitwise", [ta]))
                                (tfun [ta, ta] ta)
            relScm = Forall (Set.fromList [tva])
                            (Set.singleton ("Ord", [ta]))
                            (tfun [ta, ta] tBool)
        in
            Map.fromList
                $ [ ("+", arithScm)
                  , ("-", arithScm)
                  , ("*", arithScm)
                  , ("/", arithScm)
                  , ("rem", arithScm)
                  , ("shift-l", bitwiseScm)
                  , ("lshift-r", bitwiseScm)
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
                  , ( "transmute"
                    , Forall (Set.fromList [tva, tvb])
                             (Set.singleton ("SameSize", [ta, tb]))
                             (TFun [ta] tb)
                    )
                  , ("deref", Forall (Set.fromList [tva]) Set.empty (TFun [TBox ta] ta))
                  , ( "store"
                    , Forall (Set.fromList [tva])
                             Set.empty
                             (TFun [ta, (TBox ta)] (TBox ta))
                    )
                  , ( "cast"
                    , Forall (Set.fromList [tva, tvb])
                             (Set.singleton ("Cast", [ta, tb]))
                             (TFun [ta] tb)
                    )
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
        Parsed.TFun ps r -> liftA2 TFun (mapM go ps) (go r)
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
        inferNonrecDef' $ Parsed.VarDef dpos lhs mayscm $ WithPos dpos $ Parsed.FunMatch
            [(params, body)]
    inferNonrecDef' (Parsed.VarDef _ lhs mayscm body) = do
        t <- fresh
        mayscm' <- checkScheme (idstr lhs) mayscm
        (body', cs) <- listen $ inferDef t mayscm' (getPos body) (infer body)
        -- TODO: Can't we get rid of this somehow? It makes our solution more complex and
        --       expensive if we have to do nested solves. Also re-solves many constraints
        --       in vain.
        (sub, ccs) <- solve cs
        env <- view envLocalDefs
        scm <- generalize (substEnv sub env)
                          (fmap _scmConstraints mayscm')
                          ccs
                          (subst sub t)
        let body'' = substExpr sub body'
        pure (idstr lhs, (scm, body''))

    inferRecDefs' ds = do
        (names, mayscms', ts) <- fmap unzip3 $ forM ds $ \d -> do
            let (name, mayscm) = case d of
                    Parsed.FunDef _ x s _ _ -> (idstr x, s)
                    Parsed.VarDef _ x s _ -> (idstr x, s)
            t <- fresh
            mayscm' <- checkScheme name mayscm
            pure (name, mayscm', t)
        let dummyDefs = Map.fromList $ zip names (map (Forall Set.empty Set.empty) ts)
        (fs, ucs) <- listen $ augment envLocalDefs dummyDefs $ mapM
            (uncurry3 inferRecDef)
            (zip3 mayscms' ts ds)
        (sub, cs) <- solve ucs
        env <- view envLocalDefs
        scms <- zipWithM
            (\s -> generalize (substEnv sub env) (fmap _scmConstraints s) cs . subst sub)
            mayscms'
            ts
        let fs' = map (mapPosd (substFunMatch sub)) fs
        pure (zip names (zip scms fs'))

    inferRecDef :: Maybe Scheme -> Type -> Parsed.Def -> Infer (WithPos FunMatch)
    inferRecDef mayscm t = \case
        Parsed.FunDef fpos _ _ params body ->
            fmap (WithPos fpos)
                $ inferDef t mayscm fpos
                $ inferFunMatch
                $ [(params, body)]
        Parsed.VarDef fpos _ _ (WithPos _ (Parsed.FunMatch cs)) ->
            fmap (WithPos fpos) $ inferDef t mayscm fpos (inferFunMatch cs)
        Parsed.VarDef _ (Id lhs) _ _ -> throwError (RecursiveVarDef lhs)

    inferDef t mayscm bodyPos inferBody = do
        whenJust mayscm $ \(Forall _ _ scmt) -> unify (Expected scmt) (Found bodyPos t)
        (t', body') <- inferBody
        unify (Expected t) (Found bodyPos t')
        pure body'

    -- | Verify that user-provided type signature schemes are valid
    checkScheme :: String -> Maybe Parsed.Scheme -> Infer (Maybe Scheme)
    checkScheme = curry $ \case
        ("main", Nothing) -> pure (Just (Forall Set.empty Set.empty mainType))
        ("main", Just s@(Parsed.Forall pos vs cs t))
            | Set.size vs /= 0 || Set.size cs /= 0 || t /= mainType -> throwError
                (WrongMainType pos s)
        (_, Nothing) -> pure Nothing
        (_, Just (Parsed.Forall pos vs cs t)) -> do
            t' <- checkType pos t
            cs' <- mapM (secondM (mapM (uncurry checkType))) (Set.toList cs)
            let s1 = Forall vs (Set.fromList cs') t'
            env <- view envLocalDefs
            s2@(Forall vs2 _ t2) <- generalize env
                                               (Just (_scmConstraints s1))
                                               Map.empty
                                               t'
            if ((vs, t') == (vs2, t2))
                then pure (Just s1)
                else throwError (InvalidUserTypeSig pos s1 s2)

infer :: Parsed.Expr -> Infer (Type, Expr)
infer (WithPos pos e) = fmap (second (WithPos pos)) $ case e of
    Parsed.Lit l -> pure (litType l, Lit l)
    Parsed.Var (Id (WithPos p "_")) -> throwError (FoundHole p)
    Parsed.Var x -> fmap (\(t, tv) -> (t, Var tv)) (lookupVar x)
    Parsed.App f as -> do
        tas <- mapM (const fresh) as
        tr <- fresh
        (tf', f') <- infer f
        case tf' of
            TFun tps _ -> unless (length tps == length tas)
                $ throwError (FunArityMismatch pos (length tps) (length tas))
            _ -> pure () -- If it's not k
        (tas', as') <- fmap unzip $ mapM infer as
        unify (Expected (TFun tas tr)) (Found (getPos f) tf')
        forM_ (zip3 as tas tas')
            $ \(a, ta, ta') -> unify (Expected ta) (Found (getPos a) ta')
        pure (tr, App f' as' tr)
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
        let tCtion = TConst tdefInst
        let t = if null cParams' then tCtion else TFun cParams' tCtion
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
    (tbody, cases') <- inferCases
        [tmatchee]
        (map (first (\pat -> WithPos (getPos pat) [pat])) cases)
    let f = WithPos pos (FunMatch (cases', [tmatchee], tbody))
    pure (tbody, App f [matchee'] tbody)

inferFunMatch :: [(Parsed.FunPats, Parsed.Expr)] -> Infer (Type, FunMatch)
inferFunMatch cases = do
    arity <- checkCasePatternsArity
    tpats <- nFresh arity
    (tbody, cases') <- inferCases tpats cases
    pure (TFun tpats tbody, (cases', tpats, tbody))
  where
    checkCasePatternsArity = case cases of
        [] -> ice "inferFunMatch: checkCasePatternsArity: fun* has no cases, arity 0"
        (pats0, _) : rest -> do
            let arity = length (unpos pats0)
            forM_ rest $ \(WithPos pos pats, _) -> unless
                (length pats == arity)
                (throwError (FunCaseArityMismatch pos arity (length pats)))
            pure arity

-- | All the patterns must be of the same types, and all the bodies must be of
--   the same type.
inferCases
    :: [Type] -- Type of matchee(s). Expected type(s) of pattern(s).
    -> [(WithPos [Parsed.Pat], Parsed.Expr)]
    -> Infer (Type, Cases)
inferCases tmatchees cases = do
    (tpatss, tbodies, cases') <- fmap unzip3 (mapM inferCase cases)
    forM_ tpatss $ zipWithM (unify . Expected) tmatchees
    tbody <- fresh
    forM_ tbodies (unify (Expected tbody))
    pure (tbody, cases')
  where
    inferCase
        :: (WithPos [Parsed.Pat], Parsed.Expr)
        -> Infer ([FoundType], FoundType, (WithPos [Pat], Expr))
    inferCase (WithPos pos ps, b) = do
        (tps, ps', pvss) <- fmap unzip3 (mapM inferPat ps)
        let pvs' = map (bimap (Parsed.idstr) (Forall Set.empty Set.empty . TVar))
                       (Map.toList (Map.unions pvss))
        (tb, b') <- withLocals pvs' (infer b)
        let tps' = zipWith Found (map getPos ps) tps
        pure (tps', Found (getPos b) tb, (WithPos pos ps', b'))

-- | Returns the type of the pattern; the pattern in the Pat format that the
--   Match module wants, and a Map from the variables bound in the pattern to
--   fresh schemes.
inferPat :: Parsed.Pat -> Infer (Type, Pat, Map (Id 'Small) TVar)
inferPat pat = fmap (\(t, p, ss) -> (t, Pat (getPos pat) t p, ss)) (inferPat' pat)
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
        Just (virt, scm) -> instantiate pos scm <&> \t -> (t, (virt, TypedVar x' t))
        Nothing -> throwError (UndefVar pos x)

withLocals :: [(String, Scheme)] -> Infer a -> Infer a
withLocals = augment envLocalDefs . Map.fromList

instantiate :: SrcPos -> Scheme -> Infer Type
instantiate pos (Forall params constraints t) = do
    s <- Map.fromList <$> zipWithM (fmap . (,)) (Set.toList params) (repeat fresh)
    forM_ constraints $ \c -> unifyClass pos (substClassConstraint s c)
    pure (subst s t)

generalize
    :: (MonadError TypeErr m)
    => Map String Scheme
    -> Maybe (Set ClassConstraint)
    -> Map ClassConstraint SrcPos
    -> Type
    -> m Scheme
generalize env mayGivenCs allCs t = fmap (\cs -> Forall vs cs t) constraints
  where
    -- A constraint should be included in a signature if the type variables include at
    -- least one of the signature's forall-qualified tvars, and the rest of the tvars
    -- exist in the surrounding environment. If a tvar is not from the signature or the
    -- environment, it comes from an inner definition, and should already have been
    -- included in that signature.
    --
    -- TODO: Maybe we should handle the propagation of class constraints in a better way,
    --       so that ones belonging to inner definitions no longer exist at this point.
    constraints =
        fmap (Set.fromList . map fst) $ flip filterM (Map.toList allCs) $ \(c, pos) ->
            let vcs = ftvClassConstraint c
                belongs =
                    any (flip Set.member vs) vcs
                        && all (\vc -> Set.member vc vs || Set.member vc ftvEnv) vcs
            in  if belongs
                    then if matchesGiven c
                        then pure True
                        else throwError (NoClassInstance pos c)
                    else pure False
    matchesGiven = case mayGivenCs of
        Just gcs -> flip Set.member gcs
        Nothing -> const True
    vs = Set.difference (ftv t) ftvEnv
    ftvEnv = Set.unions (map ftvScheme (Map.elems env))
    ftvScheme (Forall tvs _ t) = Set.difference (ftv t) tvs

substEnv :: Subst' -> Map String Scheme -> Map String Scheme
substEnv s = over (mapped . scmBody) (subst s)

ftvClassConstraint :: ClassConstraint -> Set TVar
ftvClassConstraint = mconcat . map ftv . snd

substClassConstraint :: Subst' -> ClassConstraint -> ClassConstraint
substClassConstraint sub = second (map (subst sub))

nFresh :: Int -> Infer [Type]
nFresh n = sequence (replicate n fresh)

fresh :: Infer Type
fresh = fmap TVar fresh'

fresh' :: Infer TVar
fresh' = fmap TVImplicit (gets head <* modify tail)

unify :: ExpectedType -> FoundType -> Infer ()
unify e f = tell ([(e, f)], [])

unifyClass :: SrcPos -> ClassConstraint -> Infer ()
unifyClass p c = tell ([], [(p, c)])

------------------------------------------------------------------------------------------
-- Constraint solver
------------------------------------------------------------------------------------------

data UnifyErr = UInfType TVar Type | UFailed Type Type

-- TODO: I actually don't really like this approach of keeping the unification solver
--       separate from the inferrer. The approach of doing it "inline" is, at least in
--       some ways, more flexible, and probably more performant. Consider this further --
--       maybe there's a big con I haven't considered or have forgotten. Will updating the
--       substitution map work well? How would it work for nested inferDefs, compared to
--       now?
solve :: Constraints -> Infer (Subst', (Map ClassConstraint SrcPos))
solve (eqcs, ccs) = do
    sub <- lift $ lift $ lift $ solveUnis Map.empty eqcs
    ccs' <- solveClassCs (map (second (substClassConstraint sub)) ccs)
    pure (sub, ccs')
  where
    solveUnis :: Subst' -> [EqConstraint] -> Except TypeErr Subst'
    solveUnis sub1 = \case
        [] -> pure sub1
        (Expected et, Found pos ft) : cs -> do
            sub2 <- withExcept (toTypeErr pos et ft) (unifies et ft)
            solveUnis (composeSubsts sub2 sub1) (map (substConstraint sub2) cs)

    solveClassCs :: [(SrcPos, ClassConstraint)] -> Infer (Map ClassConstraint SrcPos)
    solveClassCs = fmap Map.unions . mapM solveClassConstraint

    solveClassConstraint
        :: (SrcPos, ClassConstraint) -> Infer (Map ClassConstraint SrcPos)
    solveClassConstraint (pos, c) = case c of
            -- Virtual classes
        ("SameSize", [ta, tb]) -> sameSize (ta, tb)
        ("Cast", [ta, tb]) -> cast (ta, tb)
        ("Num", [ta]) -> case ta of
            TPrim _ -> ok
            TVar _ -> propagate
            TConst _ -> err
            TFun _ _ -> err
            TBox _ -> err
        ("Bitwise", [ta]) -> case ta of
            TPrim p | isIntegral p -> ok
            TPrim _ -> err
            TVar _ -> propagate
            TConst _ -> err
            TFun _ _ -> err
            TBox _ -> err
        ("Ord", [ta]) -> case ta of
            TPrim _ -> ok
            TVar _ -> propagate
            TConst _ -> err
            TFun _ _ -> err
            TBox _ -> err
        -- "Real classes"
        -- ... TODO
        _ -> ice $ "solveClassCs: invalid class constraint " ++ show c
      where
        ok = pure Map.empty
        propagate = pure (Map.singleton c pos)
        err = throwError (NoClassInstance pos c)
        isIntegral = \case
            TInt _ -> True
            TIntSize -> True
            TNat _ -> True
            TNatSize -> True
            _ -> False

        -- TODO: Maybe we should move the check against user-provided explicit signature from
        --       `generalize` to here. Like, we could keep the explicit scheme (if there is
        --       one) in the `Env`.
        --
        -- | As the name indicates, a predicate that is true / class that is instanced when
        --   two types are of the same size. If the size for either cannot be determined yet
        --   due to polymorphism, the constraint is propagated.
        sameSize :: (Type, Type) -> Infer (Map ClassConstraint SrcPos)
        sameSize (ta, tb) = do
            sizeof' <- fmap sizeof (view envTypeDefs)
            case liftA2 (==) (sizeof' ta) (sizeof' tb) of
                _ | ta == tb -> ok
                Just True -> ok
                Just False -> err
                -- One or both of the two types are of unknown size due to polymorphism, so
                -- propagate the constraint to the scheme of the definition.
                Nothing -> propagate

        -- | This class is instanced when the first type can be `cast` to the other.
        cast :: (Type, Type) -> Infer (Map ClassConstraint SrcPos)
        cast = \case
            (ta, tb) | ta == tb -> ok
            (TPrim _, TPrim _) -> ok
            (TVar _, _) -> propagate
            (_, TVar _) -> propagate
            (TConst _, _) -> err
            (_, TConst _) -> err
            (TFun _ _, _) -> err
            (_, TFun _ _) -> err
            (TBox _, _) -> err
            (_, TBox _) -> err

    substConstraint sub (Expected t1, Found pos t2) =
        (Expected (subst sub t1), Found pos (subst sub t2))

    toTypeErr :: SrcPos -> Type -> Type -> UnifyErr -> TypeErr
    toTypeErr pos t1 t2 = \case
        UInfType a t -> InfType pos t1 t2 a t
        UFailed t'1 t'2 -> UnificationFailed pos t1 t2 t'1 t'2

-- FIXME: Keep track of whether we've flipped the arguments. Alternatively, keep right
--        stuff to the right and vice versa. If we don't, we get confusing type errors.
unifies :: Type -> Type -> Except UnifyErr Subst'
unifies = curry $ \case
    (TPrim a, TPrim b) | a == b -> pure Map.empty
    (TConst (c0, ts0), TConst (c1, ts1)) | c0 == c1 -> if length ts0 /= length ts1
        then ice "lengths of TConst params differ in unify"
        else unifiesMany (zip ts0 ts1)
    (TVar a, TVar b) | a == b -> pure Map.empty
    (TVar a, t) | occursIn a t -> throwError (UInfType a t)
    -- Do not allow "override" of explicit (user given) type variables.
    (a@(TVar (TVExplicit _)), b@(TVar (TVImplicit _))) -> unifies b a
    (a@(TVar (TVExplicit _)), b) -> throwError (UFailed a b)
    (TVar a, t) -> pure (Map.singleton a t)
    (t, TVar a) -> unifies (TVar a) t
    (t@(TFun ts1 t2), u@(TFun us1 u2)) -> if length ts1 /= length us1
        then throwError (UFailed t u)
        else unifiesMany (zip (ts1 ++ [t2]) (us1 ++ [u2]))
    (TBox t, TBox u) -> unifies t u
    (t1, t2) -> throwError (UFailed t1 t2)
  where
    unifiesMany :: [(Type, Type)] -> Except UnifyErr Subst'
    unifiesMany = foldM
        (\s (t, u) -> fmap (flip composeSubsts s) (unifies (subst s t) (subst s u)))
        Map.empty

    occursIn :: TVar -> Type -> Bool
    occursIn a t = Set.member a (ftv t)
