{-# LANGUAGE LambdaCase, DataKinds, TupleSections, FlexibleContexts #-}

module Check (typecheck) where

import Prelude hiding (span)
import Control.Monad.Except
import Control.Monad.Reader
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import Control.Applicative
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Maybe

import Misc
import SrcPos
import Subst
import qualified Ast
import Ast (Id(..), IdCase(..), idstr, Type(..), TVar(..), TPrim(..))
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
    let mTypeDefs = fmap (map fst . snd) tdefs'
    desugared <- compileDecisionTreesAndDesugar mTypeDefs substd
    checkStartDefined desugared
    let tdefs'' = fmap (second (map snd)) tdefs'
    pure (Des.Program desugared tdefs'' externs')
  where
    checkStartDefined ds =
        when (not (Map.member "start" ds)) (throwError StartNotDefined)

checkTypeDefs :: [Ast.TypeDef] -> Except TypeErr (An.TypeDefs, An.Ctors)
checkTypeDefs tdefs = do
    (tdefs', ctors) <- checkTypeDefsNoConflicting tdefs
    let tdefs'' = fmap (second (map snd)) tdefs'
    forM_ (Map.toList tdefs')
        $ \tdef -> checkTConstsDefs tdefs'' tdef *> assertNoRec tdefs' tdef
    pure (tdefs'', ctors)
  where
    -- | Check that constructurs don't refer to undefined types and that TConsts
    --   are of correct arity.
    checkTConstsDefs tds (_, (_, cs)) = forM_ cs (checkTConstsCtor tds)
    checkTConstsCtor tds (cpos, (_, ts)) = forM_ ts (checkType' tds cpos)
    -- | Check that type definitions are not recursive without indirection and
    --   that constructors don't refer to undefined types.
    assertNoRec tds (x, (_, cs)) = assertNoRecCtors tds x Map.empty cs
    assertNoRecCtors tds x s =
        mapM_ $ \(cpos, (_, ts)) ->
            forM_ ts (assertNoRecType tds x cpos . subst s)
    assertNoRecType tds x cpos = \case
        TVar _ -> pure ()
        TPrim _ -> pure ()
        TConst (y, ts) -> do
            when (x == y) $ throwError (RecTypeDef x cpos)
            let (tvs, cs) = tds Map.! y
            let substs = Map.fromList (zip tvs ts)
            assertNoRecCtors tds x substs cs
        TFun _ _ -> pure ()
        TBox _ -> pure ()

-- | Check that there are no conflicting type names or constructor names.
checkTypeDefsNoConflicting
    :: [Ast.TypeDef]
    -> Except
           TypeErr
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
    -> Except
           TypeErr
           ( (String, ([TVar], [(SrcPos, (String, [Type]))]))
           , Map
                 String
                 (Id 'Big, (VariantIx, (String, [TVar]), [Type], Span))
           )
checkTypeDef (Ast.TypeDef x' ps (Ast.ConstructorDefs cs)) = do
    let x = idstr x'
    let ps' = map TVExplicit ps
    let cs' = map (\(Id (WithPos p y), ts) -> (p, (y, ts))) cs
    let cSpan = fromIntegral (length cs)
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
    let cSpan = fromIntegral (length cs)
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
    , ( "Pair"
      , [TVImplicit 0, TVImplicit 1]
      , [("Pair", [TVar (TVImplicit 0), TVar (TVImplicit 1)])]
      )
    ]

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
        TVar tv -> do
            bound <- ask
            when (not (Set.member tv bound)) (throwError (UnboundTVar pos))
        TPrim _ -> pure ()
        TConst (_, ts) -> forM_ ts (boundInType pos)
        TFun ft at -> forM_ [ft, at] (boundInType pos)
        TBox t -> boundInType pos t
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
    compExpr (WithPos pos e) = case e of
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
                (\(p, pt) (bt, b) -> (TFun pt bt, Des.Fun (p, pt) (b, bt)))
                (TConst inst, Des.Ction v span' inst args)
                params
        An.Box x -> fmap Des.Box (compExpr x)
        An.Deref x -> fmap Des.Deref (compExpr x)
