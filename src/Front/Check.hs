{-# LANGUAGE DataKinds #-}

module Front.Check (typecheck) where

import Prelude hiding (span)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import Data.Functor
import Control.Applicative
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Misc
import Front.SrcPos
import Front.Subst
import qualified Front.Parsed as Parsed
import Front.Parsed (Id(..), TVar(..), idstr)
import Front.Err
import qualified Front.Inferred as Inferred
import Front.Match
import Front.Infer
import Front.TypeAst
import qualified Front.Checked as Checked
import Front.Checked (Virt(..))


typecheck :: Parsed.Program -> Either TypeErr Checked.Program
typecheck (Parsed.Program defs tdefs externs) = runExcept $ do
    (tdefs', ctors) <- checkTypeDefs tdefs
    externs' <- checkExterns tdefs' externs
    inferred <- inferTopDefs tdefs' ctors externs' defs
    let bound = unboundTypeVarsToUnit inferred
    -- Remove aliases. They are should be replaced in the AST and no longer needed at this point.
    let tdefs'' = Map.mapMaybe
            (secondM $ \case
                Inferred.Data rhs -> Just rhs
                Inferred.Alias _ _ -> Nothing
            )
            tdefs'
    let mTypeDefs = fmap (map (unpos . fst) . snd) tdefs''
    compiled <- compileDecisionTrees mTypeDefs bound
    checkMainDefined compiled
    let tdefs''' = fmap (second (map (first unpos))) tdefs''
    pure (Checked.Program compiled tdefs''' externs')
  where
    checkMainDefined ds =
        unless ("main" `elem` map fst (Checked.flattenDefs ds)) (throwError MainNotDefined)

type CheckTypeDefs a
    = ReaderT
          (Map String (Either Int ([TVar], Parsed.Type)))
          (StateT (Inferred.TypeDefs, Inferred.Ctors) (Except TypeErr))
          a

checkTypeDefs :: [Parsed.TypeDef] -> Except TypeErr (Inferred.TypeDefs, Inferred.Ctors)
checkTypeDefs tdefs = do
    let tdefs' = Map.union (fmap (Left . length . fst) builtinTypeDefs) $ Map.fromList
            (map
                (\case
                    Parsed.TypeDef x ps _ -> (idstr x, Left (length ps))
                    Parsed.TypeAlias x ps t -> (idstr x, Right (map TVExplicit ps, t))
                )
                tdefs
            )
    (tdefs', ctors) <- execStateT (runReaderT (forM_ tdefs checkTypeDef) tdefs')
                                  (builtinTypeDefs, builtinConstructors)
    forM_ (Map.toList tdefs') (assertNoRec tdefs')
    pure (tdefs', ctors)

checkTypeDef :: Parsed.TypeDef -> CheckTypeDefs ()
checkTypeDef = \case
    Parsed.TypeDef (Parsed.Id x) ps cs -> do
        checkNotAlreadyDefined x
        let ps' = map TVExplicit ps
        cs' <- checkCtors (unpos x, ps') cs
        forM_ (foldMap (foldMap Inferred.ftv . snd) cs')
            $ \tv -> unless (tv `elem` ps') (throwError (FreeVarsInData (getPos x) tv))
        modify (first (Map.insert (unpos x) (ps', Inferred.Data cs')))
    Parsed.TypeAlias (Parsed.Id x) ps t -> do
        checkNotAlreadyDefined x
        let ps' = map TVExplicit ps
        t' <- checkType' (getPos x) t
        forM_ (Inferred.ftv t')
            $ \tv -> unless (tv `elem` ps') (throwError (FreeVarsInAlias (getPos x) tv))
        modify (first (Map.insert (unpos x) (ps', Inferred.Alias (getPos x) t')))
  where
    checkNotAlreadyDefined (WithPos xpos x) = do
        alreadyDefined <- gets (Map.member x . fst)
        when alreadyDefined (throwError (ConflictingTypeDef xpos x))

checkCtors
    :: (String, [TVar])
    -> Parsed.ConstructorDefs
    -> CheckTypeDefs [(WithPos String, [Inferred.Type])]
checkCtors parent (Parsed.ConstructorDefs cs) =
    let cspan = fromIntegral (length cs) in mapM (checkCtor cspan) (zip [0 ..] cs)
  where
    checkCtor cspan (i, (Id c'@(WithPos pos c), ts)) = do
        cAlreadyDefined <- gets (Map.member c . snd)
        when cAlreadyDefined (throwError (ConflictingCtorDef pos c))
        ts' <- mapM (checkType' pos) ts
        modify (second (Map.insert c (i, parent, ts', cspan)))
        pure (c', ts')

checkType' :: SrcPos -> Parsed.Type -> CheckTypeDefs Inferred.Type
checkType' pos t = do
    tdefs <- ask
    let checkTConst (x, args) = case Map.lookup x tdefs of
            Nothing -> throwError (UndefType pos x)
            Just (Left expectedN) ->
                let foundN = length args
                in  if expectedN == foundN
                        then do
                            args' <- mapM go args
                            pure (TConst (x, args'))
                        else throwError (TypeInstArityMismatch pos x expectedN foundN)
            Just (Right (params, u)) -> subst (Map.fromList (zip params args)) <$> go u
        go = checkType checkTConst
    go t

builtinTypeDefs :: Inferred.TypeDefs
builtinTypeDefs = Map.fromList $ map
    (\(x, ps, cs) ->
        (x, (ps, Inferred.Data $ map (first (WithPos (SrcPos "<builtin>" 0 0 Nothing))) cs))
    )
    builtinDataTypes'

builtinConstructors :: Inferred.Ctors
builtinConstructors = Map.unions (map builtinConstructors' builtinDataTypes')
  where
    builtinConstructors' (x, ps, cs) =
        let cSpan = fromIntegral (length cs)
        in  foldl' (\csAcc (i, (cx, cps)) -> Map.insert cx (i, (x, ps), cps, cSpan) csAcc)
                   Map.empty
                   (zip [0 ..] cs)

builtinDataTypes' :: [(String, [TVar], [(String, [Inferred.Type])])]
builtinDataTypes' =
    [ ( "Array"
      , [TVImplicit "a"]
      , [("Array", [Inferred.TBox (Inferred.TVar (TVImplicit "a")), Inferred.TPrim TNatSize])]
      )
    , ("Str", [], [("Str", [tArray (Inferred.TPrim (TNat 8))])])
    , ( "Cons"
      , [TVImplicit "a", TVImplicit "b"]
      , [("Cons", [Inferred.TVar (TVImplicit "a"), Inferred.TVar (TVImplicit "b")])]
      )
    , ("Unit", [], [unit'])
    , ("RealWorld", [], [("UnsafeRealWorld", [])])
    , ("Bool", [], [("False", []), ("True", [])])
    ]
    where unit' = ("Unit", [])

assertNoRec :: Inferred.TypeDefs -> (String, ([TVar], Inferred.TypeDefRhs)) -> Except TypeErr ()
assertNoRec tdefs' (x, (xinst, rhs)) = assertNoRec' (Set.singleton (x, map TVar xinst))
                                                    rhs
                                                    Map.empty
  where
    assertNoRec' seen (Inferred.Data cs) s =
        forM_ cs $ \(WithPos cpos _, cts) -> forM_ cts (assertNoRecType seen cpos . subst s)
    assertNoRec' seen (Inferred.Alias pos t) s = assertNoRecType seen pos (subst s t)
    assertNoRecType seen cpos = \case
        Inferred.TConst (y, yinst) -> do
            when (Set.member (y, yinst) seen) $ throwError (RecTypeDef x cpos)
            let (tvs, cs) = Map.findWithDefault
                    (ice $ "assertNoRec: type id " ++ show y ++ " not in tdefs")
                    y
                    tdefs'
            let substs = Map.fromList (zip tvs yinst)
            assertNoRec' (Set.insert (y, yinst) seen) cs substs
        _ -> pure ()

checkExterns :: Inferred.TypeDefs -> [Parsed.Extern] -> Except TypeErr Inferred.Externs
checkExterns tdefs = fmap (Map.union Checked.builtinExterns . Map.fromList) . mapM checkExtern
  where
    checkExtern (Parsed.Extern name t) = do
        t' <- checkType (checkTConst tdefs (getPos name)) t
        case Set.lookupMin (Inferred.ftv t') of
            Just tv -> throwError (ExternNotMonomorphic name tv)
            Nothing -> pure (idstr name, t')

-- Any free / unbound type variables left in the AST after Infer are replacable with any
-- type, unless there's a bug in the compiler. Therefore, replace them all with Unit now.
unboundTypeVarsToUnit :: Inferred.Defs -> Inferred.Defs
unboundTypeVarsToUnit (Topo defs) = Topo $ runReader (mapM goDef defs) Set.empty
  where
    goDef :: Inferred.Def -> Reader (Set TVar) Inferred.Def
    goDef = \case
        Inferred.VarDef d -> Inferred.VarDef <$> secondM (goDefRhs goExpr) d
        Inferred.RecDefs ds -> Inferred.RecDefs <$> mapM (secondM (goDefRhs goFun)) ds

    goDefRhs f (scm, x) = (scm, ) <$> local (Set.union (Inferred._scmParams scm)) (f x)

    goMatch :: Inferred.Match -> Reader (Set TVar) Inferred.Match
    goMatch (WithPos pos (ms, cs, tps, tb)) = do
        ms' <- mapM goExpr ms
        cs' <- mapM (bimapM (mapPosdM (mapM goPat)) goExpr) cs
        tps' <- mapM subst tps
        tb' <- subst tb
        pure (WithPos pos (ms', cs', tps', tb'))

    goFun :: Inferred.Fun -> Reader (Set TVar) Inferred.Fun
    goFun (params, body) = liftA2 (,) (mapM (secondM subst) params) (bimapM goExpr subst body)

    goExpr :: Inferred.Expr -> Reader (Set TVar) Inferred.Expr
    goExpr = \case
        Inferred.Lit c -> pure (Inferred.Lit c)
        Inferred.Var v -> Inferred.Var <$> secondM goTypedVar v
        Inferred.App f as tr -> liftA3 Inferred.App (goExpr f) (mapM goExpr as) (subst tr)
        Inferred.If p c a -> liftA3 Inferred.If (goExpr p) (goExpr c) (goExpr a)
        Inferred.Let ld b -> liftA2 Inferred.Let (goDef ld) (goExpr b)
        Inferred.Fun f -> fmap Inferred.Fun (goFun f)
        Inferred.Match m -> fmap Inferred.Match (goMatch m)
        Inferred.Ctor v sp inst ts ->
            liftA2 (Inferred.Ctor v sp) (secondM (mapM subst) inst) (mapM subst ts)
        Inferred.Sizeof t -> fmap Inferred.Sizeof (subst t)

    goPat :: Inferred.Pat -> Reader (Set TVar) Inferred.Pat
    goPat (Inferred.Pat pos t pat) = liftA2 (Inferred.Pat pos) (subst t) $ case pat of
        Inferred.PVar v -> fmap Inferred.PVar (goTypedVar v)
        Inferred.PWild -> pure Inferred.PWild
        Inferred.PCon con ps -> liftA2
            Inferred.PCon
            (fmap (\ts -> con { argTs = ts }) (mapM subst (argTs con)))
            (mapM goPat ps)
        Inferred.PBox p -> fmap Inferred.PBox (goPat p)

    goTypedVar (Inferred.TypedVar x t) = fmap (Inferred.TypedVar x) (subst t)

    subst :: Inferred.Type -> Reader (Set TVar) Inferred.Type
    subst t =
        ask <&> \bound -> subst' (\tv -> if Set.member tv bound then Nothing else Just tUnit) t

compileDecisionTrees :: MTypeDefs -> Inferred.Defs -> Except TypeErr Checked.Defs
compileDecisionTrees tdefs = compDefs
  where
    compDefs (Topo defs) = Topo <$> mapM compDef defs

    compDef :: Inferred.Def -> Except TypeErr Checked.Def
    compDef = \case
        Inferred.VarDef (lhs, rhs) -> fmap (Checked.VarDef . (lhs, )) (secondM compExpr rhs)
        Inferred.RecDefs ds -> fmap Checked.RecDefs $ forM ds $ secondM (secondM compFun)

    compFun (params, (body, tbody)) = do
        body' <- compExpr body
        pure (params, (body', tbody))

    compMatch :: Inferred.Match -> Except TypeErr Checked.Expr
    compMatch (WithPos pos (ms, cs, tps, tb)) = do
        ms' <- mapM compExpr ms
        cs' <- mapM (secondM compExpr) cs
        case runExceptT (toDecisionTree tdefs pos tps cs') of
            Nothing -> pure (Checked.Absurd tb)
            Just e -> do
                dt <- liftEither e
                pure (Checked.Match ms' dt)

    compExpr :: Inferred.Expr -> Except TypeErr Checked.Expr
    compExpr ex = case ex of
        Inferred.Lit c -> pure (Checked.Lit c)
        Inferred.Var (virt, Inferred.TypedVar x t) ->
            pure (Checked.Var (virt, Checked.TypedVar x t))
        Inferred.App f as _ -> liftA2 Checked.App (compExpr f) (mapM compExpr as)
        Inferred.If p c a -> liftA3 Checked.If (compExpr p) (compExpr c) (compExpr a)
        Inferred.Let ld b -> liftA2 Checked.Let (compDef ld) (compExpr b)
        Inferred.Fun f -> fmap Checked.Fun (compFun f)
        Inferred.Match m -> compMatch m
        Inferred.Ctor v span' inst ts ->
            let xs = map (\n -> "x" ++ show n) (take (length ts) [0 ..] :: [Word])
                params = zip xs ts
                args = map (Checked.Var . (NonVirt, ) . uncurry Checked.TypedVar) params
                ret = Checked.Ction v span' inst args
                tret = Inferred.TConst inst
            in  pure $ if null params then ret else Checked.Fun (params, (ret, tret))
        Inferred.Sizeof t -> pure (Checked.Sizeof t)
