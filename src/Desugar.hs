{-# LANGUAGE LambdaCase #-}

module Desugar (desugar) where

import Data.Bifunctor
import qualified Data.Map as Map

import SrcPos
import qualified AnnotAst as An
import DesugaredAst

desugar :: An.Defs -> Defs
desugar = desugarDefs

desugarDefs :: An.Defs -> Defs
desugarDefs = fmap (second desugarExpr)

desugarExpr :: An.Expr -> Expr
desugarExpr (WithPos _ e) = case e of
    An.Lit c -> Lit c
    An.Var v -> Var (desugarTypedVar v)
    An.App f a rt -> App (desugarExpr f) (desugarExpr a) rt
    An.If p c a -> If (desugarExpr p) (desugarExpr c) (desugarExpr a)
    An.Fun p b -> Fun p (first desugarExpr b)
    An.Let ds b -> Let (desugarDefs ds) (desugarExpr b)
    An.Match m dt t -> Match (desugarExpr m) (desugarDecTree dt) t
    An.FunMatch dt pt bt ->
        let x = "#x"
        in Fun (x, pt) (Match (Var (TypedVar x pt)) (desugarDecTree dt) bt, bt)
    An.Ctor v span' inst ts ->
        let
            xs = map (\n -> "#x" ++ show n) (take (length ts) [0 :: Word ..])
            params = zip xs ts
            args = map (Var . uncurry TypedVar) params
        in snd $ foldr
            (\(p, pt) (bt, b) -> (TFun pt bt, Fun (p, pt) (b, bt)))
            (TConst inst, Ction v span' inst args)
            params
    An.Box e -> Box (desugarExpr e)
    An.Deref e -> Deref (desugarExpr e)

desugarDecTree :: An.DecisionTree -> DecisionTree
desugarDecTree = \case
    An.DLeaf (bs, e) -> DLeaf (Map.mapKeys desugarTypedVar bs, desugarExpr e)
    An.DSwitch a cs def ->
        DSwitch a (fmap desugarDecTree cs) (desugarDecTree def)

desugarTypedVar :: An.TypedVar -> TypedVar
desugarTypedVar (An.TypedVar (WithPos _ x) t) = TypedVar x t
