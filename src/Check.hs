{-# LANGUAGE LambdaCase, DataKinds, TupleSections, FlexibleContexts #-}

module Check (typecheck) where

import Prelude hiding (span)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import Control.Applicative
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Misc
import SrcPos
import Subst
import qualified Parsed
import Parsed (Id(..), TVar(..), TPrim(..), idstr)
import Err
import qualified Inferred
import Match
import Infer
import qualified Checked
import Checked (withPos, noPos)


typecheck :: Parsed.Program -> Either TypeErr Checked.Program
typecheck (Parsed.Program defs tdefs externs) = runExcept $ do
    (tdefs', ctors) <- checkTypeDefs tdefs
    externs' <- checkExterns tdefs' externs
    (inferred, substs) <- inferTopDefs tdefs' ctors externs' defs
    let substd = substTopDefs substs inferred
    checkTypeVarsBound substd
    let mTypeDefs = fmap (map (unpos . fst) . snd) tdefs'
    compiled <- compileDecisionTrees mTypeDefs substd
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
    (\(x, ps, cs) -> (x, (ps, map (first (WithPos (SrcPos "<builtin>" 0 0))) cs)))
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
      , [TVImplicit 0]
      , [("Array", [Inferred.TBox (Inferred.TVar (TVImplicit 0)), Inferred.TPrim TNat])]
      )
    , ("Str", [], [("Str", [Inferred.TConst ("Array", [Inferred.TPrim TNat8])])])
    , ( "Pair"
      , [TVImplicit 0, TVImplicit 1]
      , [("Pair", [Inferred.TVar (TVImplicit 0), Inferred.TVar (TVImplicit 1)])]
      )
    , ("Unit", [], [("Unit", [])])
    , ("Bool", [], [("False", []), ("True", [])])
    ]

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
checkExterns tdefs = fmap (Map.union Inferred.builtinExterns . Map.fromList)
    . mapM checkExtern
  where
    checkExtern (Parsed.Extern name t) = do
        t' <- checkType' tdefs (getPos name) t
        case Set.lookupMin (Inferred.ftv t') of
            Just tv -> throwError (ExternNotMonomorphic name tv)
            Nothing -> pure (idstr name, (t', getPos name))

type Bound = ReaderT (Set TVar) (Except TypeErr) ()

-- TODO: Many of these positions are weird and kind of arbitrary, man. They may
--       not align with where the type variable is actually detected.
checkTypeVarsBound :: Inferred.Defs -> Except TypeErr ()
checkTypeVarsBound ds = runReaderT (boundInDefs ds) Set.empty
  where
    boundInDefs :: Inferred.Defs -> Bound
    boundInDefs = mapM_ (secondM boundInDef) . Inferred.flattenDefs
    boundInDef (WithPos _ ((Inferred.Forall tvs _), e)) =
        local (Set.union tvs) (boundInExpr e)
    boundInExpr (WithPos pos e) = case e of
        Inferred.Lit _ -> pure ()
        Inferred.Var (Inferred.TypedVar _ t) -> boundInType pos t
        Inferred.App f a rt -> do
            boundInExpr f
            boundInExpr a
            boundInType pos rt
        Inferred.If p c a -> do
            boundInExpr p
            boundInExpr c
            boundInExpr a
        Inferred.Let ld b -> do
            mapM_ (secondM boundInDef) (Inferred.defToVarDefs ld)
            boundInExpr b
        Inferred.FunMatch (cs, pt, bt) -> do
            boundInCases cs
            boundInType pos pt
            boundInType pos bt
        Inferred.Ctor _ _ (_, instTs) ts -> do
            forM_ instTs (boundInType pos)
            forM_ ts (boundInType pos)
        Inferred.Sizeof _t -> pure ()
        Inferred.Deref x -> boundInExpr x
        Inferred.Store x p -> boundInExpr x *> boundInExpr p
    boundInType :: SrcPos -> Inferred.Type -> Bound
    boundInType pos = \case
        Inferred.TVar tv -> do
            bound <- ask
            when (not (Set.member tv bound)) (throwError (UnboundTVar pos))
        Inferred.TPrim _ -> pure ()
        Inferred.TConst (_, ts) -> forM_ ts (boundInType pos)
        Inferred.TFun ft at -> forM_ [ft, at] (boundInType pos)
        Inferred.TBox t -> boundInType pos t
    boundInCases cs = forM_ cs (bimapM boundInPat boundInExpr)
    boundInPat (WithPos pos pat) = case pat of
        Inferred.PVar (Inferred.TypedVar _ t) -> boundInType pos t
        Inferred.PWild -> pure ()
        Inferred.PCon con ps -> boundInCon pos con *> forM_ ps boundInPat
        Inferred.PBox p -> boundInPat p
    boundInCon pos (Con _ _ ts) = forM_ ts (boundInType pos)

compileDecisionTrees :: MTypeDefs -> Inferred.Defs -> Except TypeErr Checked.Defs
compileDecisionTrees tdefs = compDefs
  where
    compDefs (Topo defs) = fmap Topo $ mapM compDef defs

    compDef :: Inferred.Def -> Except TypeErr Checked.Def
    compDef = \case
        Inferred.VarDef (lhs, WithPos p rhs) ->
            fmap (Checked.VarDef . (lhs, ) . WithPos p) (secondM compExpr rhs)
        Inferred.RecDefs ds -> fmap Checked.RecDefs $ flip mapM ds $ secondM $ mapPosdM
            (secondM compFunMatch)

    compFunMatch :: WithPos Inferred.FunMatch -> Except TypeErr (WithPos Checked.Fun)
    compFunMatch (WithPos pos (cs, tp, tb)) = do
        cs' <- mapM (secondM compExpr) cs
        let p = "#x"
        fmap (WithPos pos) $ case runExceptT (toDecisionTree tdefs pos tp cs') of
            Nothing -> pure ((p, tp), (noPos (Checked.Absurd tb), tb))
            Just e -> do
                dt <- liftEither e
                let v = noPos (Checked.Var (Checked.TypedVar p tp))
                    b = noPos (Checked.Match v dt tb)
                pure ((p, tp), (b, tb))

    compExpr :: Inferred.Expr -> Except TypeErr Checked.Expr
    compExpr (WithPos pos ex) = fmap (withPos pos) $ case ex of
        Inferred.Lit c -> pure (Checked.Lit c)
        Inferred.Var (Inferred.TypedVar (WithPos _ x) t) ->
            pure (Checked.Var (Checked.TypedVar x t))
        Inferred.App f a tr -> liftA3 Checked.App (compExpr f) (compExpr a) (pure tr)
        Inferred.If p c a -> liftA3 Checked.If (compExpr p) (compExpr c) (compExpr a)
        Inferred.Let ld b -> liftA2 Checked.Let (compDef ld) (compExpr b)
        Inferred.FunMatch fm ->
            fmap (Checked.Fun . unpos) (compFunMatch (WithPos pos fm))
        Inferred.Ctor v span' inst ts ->
            let xs = map (\n -> "x" ++ show n) (take (length ts) [0 ..] :: [Word])
                params = zip xs ts
                args = map (noPos . Checked.Var . uncurry Checked.TypedVar) params
            in  pure $ snd $ foldr
                    (\(p, pt) (bt, b) ->
                        (Inferred.TFun pt bt, Checked.Fun ((p, pt), (withPos pos b, bt)))
                    )
                    (Inferred.TConst inst, Checked.Ction v span' inst args)
                    params
        Inferred.Sizeof t -> pure (Checked.Sizeof t)
        Inferred.Deref x -> fmap Checked.Deref (compExpr x)
        Inferred.Store x p -> liftA2 Checked.Store (compExpr x) (compExpr p)
