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
import Desugar
import qualified DesugaredAst as Des


typecheck :: Ast.Program -> Either TypeErr Des.Program
typecheck (Ast.Program defs tdefs externs) = runExcept $ do
    (tdefs', ctors) <- checkTypeDefs tdefs
    (externs', inferred, substs) <- inferTopDefs ctors externs defs
    let substd = substTopDefs substs inferred
    checkTypeVarsBound substd
    let mTypeDefs = fmap (map fst . snd) tdefs'
    checked <- checkPatternMatches mTypeDefs substd
    let desugared = desugar checked
    let tdefs'' = fmap (second (map snd)) tdefs'
    pure (Des.Program desugared tdefs'' externs')

checkTypeDefs :: [Ast.TypeDef] -> Except TypeErr (An.TypeDefs, An.Ctors)
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
checkTypeVarsBound :: An.Defs An.Cases -> Except TypeErr ()
checkTypeVarsBound ds = runReaderT (boundInDefs ds) Set.empty
  where
    boundInDefs :: An.Defs An.Cases -> Bound
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
        An.Match m cs tp tb -> do
            boundInExpr m
            boundInCases cs
            boundInType pos tp
            boundInType pos tb
        An.FunMatch cs pt bt -> do
            boundInCases cs
            boundInType pos pt
            boundInType pos bt
        An.Ctor _ _ (_, instTs) ts -> do
            forM_ instTs (boundInType pos)
            forM_ ts (boundInType pos)
        An.Box x -> boundInExpr x
        An.Deref x -> boundInExpr x
        An.Absurd t -> boundInType pos t
    boundInType :: SrcPos -> An.Type -> Bound
    boundInType pos = \case
        TVar tv -> do
            bound <- ask
            when (not (Set.member tv bound)) (throwError (UnboundTVar pos))
        TPrim _ -> pure ()
        TConst (_, ts) -> forM_ ts (boundInType pos)
        TFun ft at -> forM_ [ft, at] (boundInType pos)
        TBox t -> boundInType pos t
    boundInCases (An.Cases cs) = forM_ cs (bimapM boundInPat boundInExpr)
    boundInPat (WithPos pos pat) = case pat of
        An.PVar (An.TypedVar _ t) -> boundInType pos t
        An.PWild -> pure ()
        An.PCon con ps -> boundInCon pos con *> forM_ ps boundInPat
        An.PBox p -> boundInPat p
    boundInCon pos (Con _ _ ts) = forM_ ts (boundInType pos)

checkPatternMatches
    :: MTypeDefs -> An.Defs An.Cases -> Except TypeErr (An.Defs An.DecisionTree)
checkPatternMatches tdefs = checkMsDefs
  where
    checkMsDefs = mapM checkMsDef
    checkMsDef = bimapM pure checkMsExpr
    checkMsExpr
        :: An.Expr An.Cases -> Except TypeErr (An.Expr An.DecisionTree)
    checkMsExpr (WithPos pos e) = fmap (WithPos pos) $ case e of
        An.Lit c -> pure (An.Lit c)
        An.Var v -> pure (An.Var v)
        An.App f a tr ->
            liftA3 An.App (checkMsExpr f) (checkMsExpr a) (pure tr)
        An.If p c a ->
            liftA3 An.If (checkMsExpr p) (checkMsExpr c) (checkMsExpr a)
        An.Let lds b -> liftA2 An.Let (checkMsDefs lds) (checkMsExpr b)
        An.Match m cs tp tb -> do
            m' <- checkMsExpr m
            toDecisionTree' pos tp cs tb (An.Match m')
        An.FunMatch cs tp tb -> toDecisionTree' pos tp cs tb An.FunMatch
        An.Ctor v s tc ts -> pure (An.Ctor v s tc ts)
        An.Box x -> fmap An.Box (checkMsExpr x)
        An.Deref x -> fmap An.Deref (checkMsExpr x)
        An.Absurd t -> pure (An.Absurd t)
    toDecisionTree' pos tp (An.Cases cs) tb f = do
        cs' <- mapM (secondM checkMsExpr) cs
        case runExceptT (toDecisionTree tdefs pos tp cs') of
            Nothing -> pure (An.Absurd tb)
            Just e -> fmap (\dt -> f dt tp tb) (liftEither e)
