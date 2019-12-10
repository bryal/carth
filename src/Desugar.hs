{-# LANGUAGE LambdaCase #-}

module Desugar (unsugar) where

import Data.Bifunctor

import qualified AnnotAst as An
import DesugaredAst

unsugar :: (An.Expr, An.Defs) -> (Expr, Defs)
unsugar (main, ds) = (unsugarExpr main, unsugarDefs ds)

unsugarDefs :: An.Defs -> Defs
unsugarDefs = fmap (second unsugarExpr)

unsugarExpr :: An.Expr -> Expr
unsugarExpr = \case
    An.Lit c -> Lit c
    An.Var tv -> Var tv
    An.App f a rt -> App (unsugarExpr f) (unsugarExpr a) rt
    An.If p c a -> If (unsugarExpr p) (unsugarExpr c) (unsugarExpr a)
    An.Fun p b -> Fun p (first unsugarExpr b)
    An.Let ds b -> Let (unsugarDefs ds) (unsugarExpr b)
    An.Match m dt t -> Match (unsugarExpr m) (unsugarDecTree dt) t
    An.FunMatch dt pt bt ->
        let x = "#x"
        in Fun (x, pt) (Match (Var (TypedVar x pt)) (unsugarDecTree dt) bt, bt)
    An.Ctor v inst ts ->
        let
            xs = map (\n -> "#x" ++ show n) (take (length ts) [0 :: Word ..])
            params = zip xs ts
            args = map (Var . uncurry TypedVar) params
        in snd $ foldr
            (\(p, pt) (bt, b) -> (TFun pt bt, Fun (p, pt) (b, bt)))
            (TConst inst, Ction v inst args)
            params

unsugarDecTree :: An.DecisionTree -> DecisionTree
unsugarDecTree = \case
    An.DLeaf (bs, e) -> DLeaf (bs, unsugarExpr e)
    An.DSwitch a cs def ->
        DSwitch a (fmap unsugarDecTree cs) (unsugarDecTree def)
