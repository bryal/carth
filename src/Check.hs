{-# LANGUAGE LambdaCase, DataKinds, TupleSections, FlexibleContexts #-}

module Check (typecheck) where

import Prelude hiding (span)
import Control.Monad.Except
import Data.Bifunctor
import Data.Foldable
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe

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
    (externs', inferred, substs) <- inferTopDefs tdefs' ctors externs defs
    let substd = substTopDefs substs inferred
    let desugared = unsugar substd
    let tdefs'' = fmap (second (map snd)) tdefs'
    pure (uncurry Des.Program desugared tdefs'' externs')

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
                 (Id Big, (VariantIx, (String, [TVar]), [Type], Span))
           )
checkTypeDef (Ast.TypeDef x' ps (Ast.ConstructorDefs cs)) = do
    let x = idstr x'
    let ps' = map TVExplicit ps
    let cs' = map (\(Id (WithPos p x), ts) -> (p, (x, ts))) cs
    let cSpan = length cs
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
    let cSpan = length cs
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
    ]
