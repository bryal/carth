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
import TypeErr
import qualified Inferred
import Match
import Infer
import qualified Checked
import Checked (withPos, noPos)


typecheck :: Parsed.Program -> Either TypeErr Checked.Program
typecheck (Parsed.Program defs tdefs externs) = runExcept $ do
    (tdefs', ctors) <- checkTypeDefs tdefs
    (externs', inferred, substs) <- inferTopDefs tdefs' ctors externs defs
    let substd = substTopDefs substs inferred
    checkTypeVarsBound substd
    let mTypeDefs = fmap (map (unpos . fst) . snd) tdefs'
    desugared <- compileDecisionTrees mTypeDefs substd
    checkStartDefined desugared
    let tdefs'' = fmap (second (map snd)) tdefs'
    pure (Checked.Program desugared tdefs'' externs')
  where
    checkStartDefined ds =
        when (not (Map.member "start" ds)) (throwError StartNotDefined)

type CheckTypeDefs a
    = ReaderT
          (Map String Int)
          (StateT (Inferred.TypeDefs, Inferred.Ctors) (Except TypeErr))
          a

checkTypeDefs
    :: [Parsed.TypeDef] -> Except TypeErr (Inferred.TypeDefs, Inferred.Ctors)
checkTypeDefs tdefs = do
    let tdefsParams =
            Map.union (fmap (length . fst) builtinDataTypes)
                $ Map.fromList
                    (map
                        (\(Parsed.TypeDef x ps _) -> (idstr x, length ps))
                        tdefs
                    )
    (tdefs', ctors) <- execStateT
        (runReaderT (forM_ tdefs checkTypeDef) tdefsParams)
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
    let cspan = fromIntegral (length cs)
    in mapM (checkCtor cspan) (zip [0 ..] cs)
  where
    checkCtor cspan (i, (Id c'@(WithPos pos c), ts)) = do
        cAlreadyDefined <- gets (Map.member c . snd)
        when cAlreadyDefined (throwError (ConflictingCtorDef pos c))
        ts' <- mapM (checkType pos) ts
        modify (second (Map.insert c (i, parent, ts', cspan)))
        pure (c', ts')
    checkType pos t =
        ask >>= \tdefs -> checkType' (\x -> Map.lookup x tdefs) pos t

builtinDataTypes :: Inferred.TypeDefs
builtinDataTypes = Map.fromList $ map
    (\(x, ps, cs) -> (x, (ps, map (first (WithPos dummyPos)) cs)))
    builtinDataTypes'

builtinConstructors :: Inferred.Ctors
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

builtinDataTypes' :: [(String, [TVar], [(String, [Inferred.Type])])]
builtinDataTypes' =
    [ ( "Array"
      , [TVImplicit 0]
      , [ ( "Array"
          , [Inferred.TBox (Inferred.TVar (TVImplicit 0)), Inferred.TPrim TNat]
          )
        ]
      )
    , ( "Str"
      , []
      , [("Str", [Inferred.TConst ("Array", [Inferred.TPrim TNat8])])]
      )
    , ( "Pair"
      , [TVImplicit 0, TVImplicit 1]
      , [("Pair", [Inferred.TVar (TVImplicit 0), Inferred.TVar (TVImplicit 1)])]
      )
    ]

assertNoRec
    :: Inferred.TypeDefs
    -> (String, ([TVar], [(Inferred.Id, [Inferred.Type])]))
    -> Except TypeErr ()
assertNoRec tdefs' (x, (_, ctors)) = assertNoRec' ctors Map.empty
  where
    assertNoRec' cs s =
        forM_ cs $ \(WithPos cpos _, cts) ->
            forM_ cts (assertNoRecType cpos . subst s)
    assertNoRecType cpos = \case
        Inferred.TConst (y, ts) -> do
            when (x == y) $ throwError (RecTypeDef x cpos)
            let (tvs, cs) = tdefs' Map.! y
            let substs = Map.fromList (zip tvs ts)
            assertNoRec' cs substs
        _ -> pure ()

type Bound = ReaderT (Set TVar) (Except TypeErr) ()

-- TODO: Many of these positions are weird and kind of arbitrary, man. They may
--       not align with where the type variable is actually detected.
checkTypeVarsBound :: Inferred.Defs -> Except TypeErr ()
checkTypeVarsBound ds = runReaderT (boundInDefs ds) Set.empty
  where
    boundInDefs :: Inferred.Defs -> Bound
    boundInDefs = mapM_ boundInDef
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
        Inferred.Let lds b -> do
            boundInDefs lds
            boundInExpr b
        Inferred.FunMatch cs pt bt -> do
            boundInCases cs
            boundInType pos pt
            boundInType pos bt
        Inferred.Ctor _ _ (_, instTs) ts -> do
            forM_ instTs (boundInType pos)
            forM_ ts (boundInType pos)
        Inferred.Box x -> boundInExpr x
        Inferred.Deref x -> boundInExpr x
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

compileDecisionTrees
    :: MTypeDefs -> Inferred.Defs -> Except TypeErr Checked.Defs
compileDecisionTrees tdefs = compDefs
  where
    compDefs = mapM compDef
    compDef (WithPos p rhs) = fmap (WithPos p) (secondM compExpr rhs)
    compExpr :: Inferred.Expr -> Except TypeErr Checked.Expr
    compExpr (WithPos pos ex) = fmap (withPos pos) $ case ex of
        Inferred.Lit c -> pure (Checked.Lit c)
        Inferred.Var (Inferred.TypedVar (WithPos _ x) t) ->
            pure (Checked.Var (Checked.TypedVar x t))
        Inferred.App f a tr ->
            liftA3 Checked.App (compExpr f) (compExpr a) (pure tr)
        Inferred.If p c a ->
            liftA3 Checked.If (compExpr p) (compExpr c) (compExpr a)
        Inferred.Let lds b ->
            liftA2 Checked.Let (compDefs lds) (compExpr b)
        Inferred.FunMatch cs tp tb -> do
            cs' <- mapM (secondM compExpr) cs
            case runExceptT (toDecisionTree tdefs pos tp cs') of
                Nothing -> pure (Checked.Absurd tb)
                Just e -> do
                    dt <- liftEither e
                    let p = "#x"
                        v = noPos (Checked.Var (Checked.TypedVar p tp))
                        b = noPos (Checked.Match v dt tb)
                    pure (Checked.Fun (p, tp) (b, tb))
        Inferred.Ctor v span' inst ts ->
            let
                xs = map
                    (\n -> "x" ++ show n)
                    (take (length ts) [0 ..] :: [Word])
                params = zip xs ts
                args = map
                    (noPos . Checked.Var . uncurry Checked.TypedVar)
                    params
            in pure $ snd $ foldr
                (\(p, pt) (bt, b) ->
                    (Inferred.TFun pt bt, Checked.Fun (p, pt) (noPos b, bt))
                )
                (Inferred.TConst inst, Checked.Ction v span' inst args)
                params
        Inferred.Box x -> fmap Checked.Box (compExpr x)
        Inferred.Deref x -> fmap Checked.Deref (compExpr x)
