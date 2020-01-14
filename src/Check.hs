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
import qualified Ast
import Ast (Id(..), IdCase(..), TVar(..), TPrim(..), idstr)
import TypeErr
import AnnotAst (VariantIx)
import qualified AnnotAst as An
import Match
import Infer
import qualified DesugaredAst as Des


typecheck :: Ast.Program -> Either TypeErr Des.Program
typecheck (Ast.Program defs tdefs externs) = runExcept $ do
    (tdefs', ctors) <- checkTypeDefs tdefs
    (externs', inferred, substs) <- inferTopDefs tdefs' ctors externs defs
    let substd = substTopDefs substs inferred
    checkTypeVarsBound substd
    let mTypeDefs = fmap (map (unpos . fst) . snd) tdefs'
    desugared <- compileDecisionTreesAndDesugar mTypeDefs substd
    checkStartDefined desugared
    let tdefs'' = fmap (second (map snd)) tdefs'
    pure (Des.Program desugared tdefs'' externs')
  where
    checkStartDefined ds =
        when (not (Map.member "start" ds)) (throwError StartNotDefined)

type CheckTypeDefs a
    = ReaderT
          (Map String Int)
          (StateT (An.TypeDefs, An.Ctors) (Except TypeErr))
          a

checkTypeDefs :: [Ast.TypeDef] -> Except TypeErr (An.TypeDefs, An.Ctors)
checkTypeDefs tdefs = do
    let tdefsParams =
            Map.union (fmap (length . fst) builtinDataTypes) $ Map.fromList
                (map (\(Ast.TypeDef x ps _) -> (idstr x, length ps)) tdefs)
    (tdefs', ctors) <- execStateT
        (runReaderT (forM_ tdefs checkTypeDef) tdefsParams)
        (builtinDataTypes, builtinConstructors)
    forM_ (Map.toList tdefs') (assertNoRec tdefs')
    pure (tdefs', ctors)

checkTypeDef :: Ast.TypeDef -> CheckTypeDefs ()
checkTypeDef (Ast.TypeDef (Ast.Id (WithPos xpos x)) ps cs) = do
    tAlreadyDefined <- gets (Map.member x . fst)
    when tAlreadyDefined (throwError (ConflictingTypeDef xpos x))
    let ps' = map TVExplicit ps
    cs' <- checkCtors (x, ps') cs
    modify (first (Map.insert x (ps', cs')))

checkCtors
    :: (String, [TVar])
    -> Ast.ConstructorDefs
    -> CheckTypeDefs [(An.Id, [An.Type])]
checkCtors parent (Ast.ConstructorDefs cs) =
    let cspan = fromIntegral (length cs)
    in mapM (checkCtor cspan) (zip [0 ..] cs)
  where
    checkCtor cspan (i, (Id c'@(WithPos pos c), ts)) = do
        cAlreadyDefined <- gets (Map.member c . snd)
        when cAlreadyDefined (throwError (ConflictingCtorDef pos c))
        ts' <- mapM checkType ts
        modify (second (Map.insert c (i, parent, ts', cspan)))
        pure (c', ts')
    checkType t =
        ask >>= \tdefs -> checkType' (\x -> Map.lookup x tdefs) pos t

builtinDataTypes :: An.TypeDefs
builtinDataTypes = Map.fromList $ map
    (\(x, ps, cs) -> (x, (ps, map (first (WithPos dummyPos)) cs)))
    builtinDataTypes'

builtinConstructors :: An.Ctors
builtinConstructors = Map.unions (map builtinConstructors' builtinDataTypes')
  where
    builtinConstructors' (x, ps, cs) =
        let cSpan = fromIntegral (length cs)
        in
            foldl'
                (\csAcc (i, (cx, cps)) ->
                    Map.insert cx (i, (x, ps), cps, cSpan) csAcc
                )
                Map.empty
                (zip [0 ..] cs)

builtinDataTypes' :: [(String, [TVar], [(String, [An.Type])])]
builtinDataTypes' =
    [ ( "Array"
      , [TVImplicit 0]
      , [("Array", [An.TBox (An.TVar (TVImplicit 0)), An.TPrim TNat])]
      )
    , ("Str", [], [("Str", [An.TConst ("Array", [An.TPrim TNat8])])])
    , ( "Pair"
      , [TVImplicit 0, TVImplicit 1]
      , [("Pair", [An.TVar (TVImplicit 0), An.TVar (TVImplicit 1)])]
      )
    ]

assertNoRec
    :: An.TypeDefs
    -> (String, ([TVar], [(An.Id, [An.Type])]))
    -> Except TypeErr ()
assertNoRec tdefs' (x, (_, ctors)) = assertNoRec' ctors Map.empty
  where
    assertNoRec' cs s =
        forM_ cs $ \(WithPos cpos _, cts) ->
            forM_ cts (assertNoRecType cpos . subst s)
    assertNoRecType cpos = \case
        An.TConst (y, ts) -> do
            when (x == y) $ throwError (RecTypeDef x cpos)
            let (tvs, cs) = tdefs' Map.! y
            let substs = Map.fromList (zip tvs ts)
            assertNoRec' cs substs
        _ -> pure ()

type Bound = ReaderT (Set TVar) (Except TypeErr) ()

-- TODO: Many of these positions are weird and kind of arbitrary, man. They may
--       not align with where the type variable is actually detected.
checkTypeVarsBound :: An.Defs -> Except TypeErr ()
checkTypeVarsBound ds = runReaderT (boundInDefs ds) Set.empty
  where
    boundInDefs :: An.Defs -> Bound
    boundInDefs = mapM_ boundInDef
    boundInDef ((An.Forall tvs _), e) =
        local (Set.union tvs) (boundInExpr e)
    boundInExpr (WithPos pos e) = case e of
        An.Lit _ -> pure ()
        An.Var (An.TypedVar _ t) -> boundInType pos t
        An.App f a rt -> do
            boundInExpr f
            boundInExpr a
            boundInType pos rt
        An.If p c a -> do
            boundInExpr p
            boundInExpr c
            boundInExpr a
        An.Let lds b -> do
            boundInDefs lds
            boundInExpr b
        An.FunMatch cs pt bt -> do
            boundInCases cs
            boundInType pos pt
            boundInType pos bt
        An.Ctor _ _ (_, instTs) ts -> do
            forM_ instTs (boundInType pos)
            forM_ ts (boundInType pos)
        An.Box x -> boundInExpr x
        An.Deref x -> boundInExpr x
    boundInType :: SrcPos -> An.Type -> Bound
    boundInType pos = \case
        An.TVar tv -> do
            bound <- ask
            when (not (Set.member tv bound)) (throwError (UnboundTVar pos))
        An.TPrim _ -> pure ()
        An.TConst (_, ts) -> forM_ ts (boundInType pos)
        An.TFun ft at -> forM_ [ft, at] (boundInType pos)
        An.TBox t -> boundInType pos t
    boundInCases cs = forM_ cs (bimapM boundInPat boundInExpr)
    boundInPat (WithPos pos pat) = case pat of
        An.PVar (An.TypedVar _ t) -> boundInType pos t
        An.PWild -> pure ()
        An.PCon con ps -> boundInCon pos con *> forM_ ps boundInPat
        An.PBox p -> boundInPat p
    boundInCon pos (Con _ _ ts) = forM_ ts (boundInType pos)

compileDecisionTreesAndDesugar
    :: MTypeDefs -> An.Defs -> Except TypeErr Des.Defs
compileDecisionTreesAndDesugar tdefs = compDefs
  where
    compDefs = mapM compDef
    compDef = bimapM pure compExpr
    compExpr :: An.Expr -> Except TypeErr Des.Expr
    compExpr (WithPos pos expr) = case expr of
        An.Lit c -> pure (Des.Lit c)
        An.Var (An.TypedVar (WithPos _ x) t) ->
            pure (Des.Var (Des.TypedVar x t))
        An.App f a tr -> liftA3 Des.App (compExpr f) (compExpr a) (pure tr)
        An.If p c a -> liftA3 Des.If (compExpr p) (compExpr c) (compExpr a)
        An.Let lds b -> liftA2 Des.Let (compDefs lds) (compExpr b)
        An.FunMatch cs tp tb -> do
            cs' <- mapM (secondM compExpr) cs
            case runExceptT (toDecisionTree tdefs pos tp cs') of
                Nothing -> pure (Des.Absurd tb)
                Just e -> do
                    dt <- liftEither e
                    let p = "#x"
                        v = Des.Var (Des.TypedVar p tp)
                        b = Des.Match v dt tb
                    pure (Des.Fun (p, tp) (b, tb))
        An.Ctor v span' inst ts ->
            let
                xs = map
                    (\n -> "#x" ++ show n)
                    (take (length ts) [0 :: Word ..])
                params = zip xs ts
                args = map (Des.Var . uncurry Des.TypedVar) params
            in pure $ snd $ foldr
                (\(p, pt) (bt, b) ->
                    (An.TFun pt bt, Des.Fun (p, pt) (b, bt))
                )
                (An.TConst inst, Des.Ction v span' inst args)
                params
        An.Box x -> fmap Des.Box (compExpr x)
        An.Deref x -> fmap Des.Deref (compExpr x)
