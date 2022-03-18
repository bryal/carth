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
    let mTypeDefs = fmap (map (unpos . fst) . snd) tdefs'
    compiled <- compileDecisionTrees mTypeDefs bound
    checkMainDefined compiled
    let tdefs'' = fmap (second (map snd)) tdefs'
    pure (Checked.Program compiled tdefs'' externs')
  where
    checkMainDefined ds = when (not (elem "main" (map fst (Checked.flattenDefs ds))))
                               (throwError MainNotDefined)

type CheckTypeDefs a
    = ReaderT
          (Map String Int)
          (StateT (Inferred.TypeDefs, Inferred.Ctors) (Except TypeErr))
          a

checkTypeDefs :: [Parsed.TypeDef] -> Except TypeErr (Inferred.TypeDefs, Inferred.Ctors)
checkTypeDefs tdefs = do
    let tdefsParams = Map.union (fmap (length . fst) builtinDataTypes) $ Map.fromList
            (map (\(Parsed.TypeDef x ps _) -> (idstr x, length ps)) tdefs)
    (tdefs', ctors) <- execStateT (runReaderT (forM_ tdefs checkTypeDef) tdefsParams)
                                  (builtinDataTypes, builtinConstructors)
    forM_ (Map.toList tdefs') (assertNoRec tdefs')
    pure (tdefs', ctors)

checkTypeDef :: Parsed.TypeDef -> CheckTypeDefs ()
checkTypeDef (Parsed.TypeDef (Parsed.Id (WithPos xpos x)) ps cs) = do
    tAlreadyDefined <- gets (Map.member x . fst)
    when tAlreadyDefined (throwError (ConflictingTypeDef xpos x))
    let ps' = map TVExplicit ps
    cs' <- checkCtors (x, ps') cs
    modify (first (Map.insert x (ps', cs')))

checkCtors
    :: (String, [TVar])
    -> Parsed.ConstructorDefs
    -> CheckTypeDefs [(Inferred.Id, [Inferred.Type])]
checkCtors parent (Parsed.ConstructorDefs cs) =
    let cspan = fromIntegral (length cs) in mapM (checkCtor cspan) (zip [0 ..] cs)
  where
    checkCtor cspan (i, (Id c'@(WithPos pos c), ts)) = do
        cAlreadyDefined <- gets (Map.member c . snd)
        when cAlreadyDefined (throwError (ConflictingCtorDef pos c))
        ts' <- mapM (checkType pos) ts
        modify (second (Map.insert c (i, parent, ts', cspan)))
        pure (c', ts')
    checkType pos t = ask >>= \tdefs -> checkType'' (\x -> Map.lookup x tdefs) pos t

builtinDataTypes :: Inferred.TypeDefs
builtinDataTypes = Map.fromList $ map
    (\(x, ps, cs) -> (x, (ps, map (first (WithPos (SrcPos "<builtin>" 0 0 Nothing))) cs)))
    builtinDataTypes'

builtinConstructors :: Inferred.Ctors
builtinConstructors = Map.unions (map builtinConstructors' builtinDataTypes')
  where
    builtinConstructors' (x, ps, cs) =
        let cSpan = fromIntegral (length cs)
        in  foldl'
                (\csAcc (i, (cx, cps)) -> Map.insert cx (i, (x, ps), cps, cSpan) csAcc)
                Map.empty
                (zip [0 ..] cs)

builtinDataTypes' :: [(String, [TVar], [(String, [Inferred.Type])])]
builtinDataTypes' =
    [ ( "Array"
      , [TVImplicit "a"]
      , [ ( "Array"
          , [Inferred.TBox (Inferred.TVar (TVImplicit "a")), Inferred.TPrim TNatSize]
          )
        ]
      )
    , ("Str", [], [("Str", [tArray (Inferred.TPrim (TNat 8))])])
    , ( "Cons"
      , [TVImplicit "a", TVImplicit "b"]
      , [("Cons", [Inferred.TVar (TVImplicit "a"), Inferred.TVar (TVImplicit "b")])]
      )
    , ("Unit", [], [unit'])
    , ("RealWorld", [], [("UnsafeRealWorld", [])])
    , ("Bool", [], [("False", []), ("True", [])])
    , ( "IO"
      , [TVImplicit "a"]
      , [ ( "IO"
          , [ Inferred.TFun [tc ("RealWorld", [])] $ tc
                  ( "Cons"
                  , [ Inferred.TVar (TVImplicit "a")
                    , tc ("Cons", [tc ("RealWorld", []), tc unit'])
                    ]
                  )
            ]
          )
        ]
      )
    ]
  where
    tc = Inferred.TConst
    unit' = ("Unit", [])

assertNoRec
    :: Inferred.TypeDefs
    -> (String, ([TVar], [(Inferred.Id, [Inferred.Type])]))
    -> Except TypeErr ()
assertNoRec tdefs' (x, (_, ctors)) = assertNoRec' ctors Map.empty
  where
    assertNoRec' cs s =
        forM_ cs $ \(WithPos cpos _, cts) -> forM_ cts (assertNoRecType cpos . subst s)
    assertNoRecType cpos = \case
        Inferred.TConst (y, ts) -> do
            when (x == y) $ throwError (RecTypeDef x cpos)
            let (tvs, cs) = tdefs' Map.! y
            let substs = Map.fromList (zip tvs ts)
            assertNoRec' cs substs
        _ -> pure ()

checkExterns :: Inferred.TypeDefs -> [Parsed.Extern] -> Except TypeErr Inferred.Externs
checkExterns tdefs = fmap (Map.union Checked.builtinExterns . Map.fromList)
    . mapM checkExtern
  where
    checkExtern (Parsed.Extern name t) = do
        t' <- checkType' tdefs (getPos name) t
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
        Inferred.VarDef d -> fmap Inferred.VarDef $ secondM (goDefRhs goExpr) d
        Inferred.RecDefs ds ->
            fmap Inferred.RecDefs $ mapM (secondM (goDefRhs (mapPosdM goFunMatch))) ds

    goDefRhs f (scm, x) =
        fmap (scm, ) $ local (Set.union (Inferred._scmParams scm)) (f x)

    goFunMatch :: Inferred.FunMatch -> Reader (Set TVar) Inferred.FunMatch
    goFunMatch (cs, tps, tb) = liftA3
        (,,)
        (mapM (bimapM (mapPosdM (mapM goPat)) goExpr) cs)
        (mapM subst tps)
        (subst tb)

    goExpr :: Inferred.Expr -> Reader (Set TVar) Inferred.Expr
    goExpr = mapPosdM $ \case
        Inferred.Lit c -> pure (Inferred.Lit c)
        Inferred.Var v -> fmap Inferred.Var $ secondM goTypedVar v
        Inferred.App f as tr ->
            liftA3 Inferred.App (goExpr f) (mapM goExpr as) (subst tr)
        Inferred.If p c a -> liftA3 Inferred.If (goExpr p) (goExpr c) (goExpr a)
        Inferred.Let ld b -> liftA2 Inferred.Let (goDef ld) (goExpr b)
        Inferred.FunMatch fm -> fmap Inferred.FunMatch (goFunMatch fm)
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
    subst t = ask <&> \bound ->
        subst' (\tv -> if Set.member tv bound then Nothing else Just tUnit) t

compileDecisionTrees :: MTypeDefs -> Inferred.Defs -> Except TypeErr Checked.Defs
compileDecisionTrees tdefs = compDefs
  where
    compDefs (Topo defs) = fmap Topo $ mapM compDef defs

    compDef :: Inferred.Def -> Except TypeErr Checked.Def
    compDef = \case
        Inferred.VarDef (lhs, rhs) ->
            fmap (Checked.VarDef . (lhs, )) (secondM compExpr rhs)
        Inferred.RecDefs ds ->
            fmap Checked.RecDefs $ flip mapM ds $ secondM (secondM compFunMatch)

    compFunMatch :: WithPos Inferred.FunMatch -> Except TypeErr Checked.Fun
    compFunMatch (WithPos pos (cs, tps, tb)) = do
        cs' <- mapM (secondM compExpr) cs
        let ps = map (("#x" ++) . show) [0 .. length tps - 1]
            vs = zipWith (\p tp -> Checked.Var (NonVirt, Checked.TypedVar p tp)) ps tps
        case runExceptT (toDecisionTree tdefs pos tps cs') of
            Nothing -> pure (zip ps tps, (Checked.Absurd tb, tb))
            Just e -> do
                dt <- liftEither e
                let b = Checked.Match vs dt
                pure (zip ps tps, (b, tb))

    compExpr :: Inferred.Expr -> Except TypeErr Checked.Expr
    compExpr (WithPos pos ex) = case ex of
        Inferred.Lit c -> pure (Checked.Lit c)
        Inferred.Var (virt, Inferred.TypedVar (WithPos _ x) t) ->
            pure (Checked.Var (virt, Checked.TypedVar x t))
        Inferred.App f as _ -> liftA2 Checked.App (compExpr f) (mapM compExpr as)
        Inferred.If p c a -> liftA3 Checked.If (compExpr p) (compExpr c) (compExpr a)
        Inferred.Let ld b -> liftA2 Checked.Let (compDef ld) (compExpr b)
        Inferred.FunMatch fm -> fmap Checked.Fun (compFunMatch (WithPos pos fm))
        Inferred.Ctor v span' inst ts ->
            let xs = map (\n -> "x" ++ show n) (take (length ts) [0 ..] :: [Word])
                params = zip xs ts
                args = map (Checked.Var . (NonVirt, ) . uncurry Checked.TypedVar) params
                ret = Checked.Ction v span' inst args
                tret = Inferred.TConst inst
            in  pure $ if null params then ret else Checked.Fun (params, (ret, tret))
        Inferred.Sizeof t -> pure (Checked.Sizeof t)
