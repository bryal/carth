{-# LANGUAGE LambdaCase #-}

module Subst
    ( Subst
    , subst
    , substProgram
    , composeSubsts
    , VarSubst
    , substVExpr
    )
where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Bifunctor
import Data.Maybe

import AnnotAst

-- | Map of substitutions from type-variables to more specific types
type Subst = Map TVar Type

type VarSubst = (String, String)

substProgram :: Subst -> Program -> Program
substProgram s (Program main (Defs defs) tdefs) =
    Program (substExpr s main) (Defs (fmap (substDef s) defs)) tdefs

substDef :: Subst -> (Scheme, Expr) -> (Scheme, Expr)
substDef s = second (substExpr s)

substExpr :: Subst -> Expr -> Expr
substExpr s = \case
    Lit c -> Lit c
    Var (TypedVar x t) -> Var (TypedVar x (subst s t))
    App f a -> App (substExpr s f) (substExpr s a)
    If p c a -> If (substExpr s p) (substExpr s c) (substExpr s a)
    Fun (p, tp) (b, bt) -> Fun (p, subst s tp) (substExpr s b, subst s bt)
    Let (Defs defs) body ->
        Let (Defs (fmap (substDef s) defs)) (substExpr s body)
    Match e dt tbody ->
        Match (substExpr s e) (substDecisionTree s dt) (subst s tbody)
    Ction (i, (tx, tts), es) ->
        Ction (i, (tx, map (subst s) tts), map (substExpr s) es)

substDecisionTree :: Subst -> DecisionTree -> DecisionTree
substDecisionTree s = \case
    DecisionTree cs vdt -> DecisionTree
        (fmap (\(ts, dt) -> (map (subst s) ts, substDecisionTree s dt)) cs)
        (fmap
            (\(TypedVar x t, dt) ->
                (TypedVar x (subst s t), substDecisionTree s dt)
            )
            vdt
        )
    DecisionLeaf e -> DecisionLeaf (substExpr s e)

subst :: Subst -> Type -> Type
subst s t = case t of
    TVar tv -> fromMaybe t (Map.lookup tv s)
    TPrim _ -> t
    TFun a b -> TFun (subst s a) (subst s b)
    TConst (c, ts) -> TConst (c, (map (subst s) ts))

composeSubsts :: Subst -> Subst -> Subst
composeSubsts s1 s2 = Map.union (fmap (subst s1) s2) s1

substVExpr :: VarSubst -> Expr -> Expr
substVExpr s = \case
    Lit c -> Lit c
    Var (TypedVar x t) -> Var (TypedVar (substV s x) t)
    App f a -> App (substVExpr s f) (substVExpr s a)
    If p c a -> If (substVExpr s p) (substVExpr s c) (substVExpr s a)
    Fun p b -> substVFun s p b
    Let (Defs defs) body -> substVLet s defs body
    Match e dt t -> Match (substVExpr s e) (substVDecisionTree s dt) t
    Ction (i, t, es) -> Ction (i, t, map (substVExpr s) es)

substVFun :: VarSubst -> (String, Type) -> (Expr, Type) -> Expr
substVFun s@(from, _) p@(p', _) b@(b', tb) =
    if p' == from then Fun p b else Fun p (substVExpr s b', tb)

substVLet :: VarSubst -> Map String (Scheme, Expr) -> Expr -> Expr
substVLet s@(from, _) defs body =
    let
        defs' = Map.mapWithKey
            (\k (scm, e) -> (scm, if from == k then e else substVExpr s e))
            defs
        body' = if Map.member from defs then body else substVExpr s body
    in Let (Defs defs') body'

substVDecisionTree :: VarSubst -> DecisionTree -> DecisionTree
substVDecisionTree s = \case
    DecisionTree cs vdt -> DecisionTree
        (fmap (\(ts, dt) -> (ts, substVDecisionTree s dt)) cs)
        (fmap
            (\(TypedVar x t, dt) ->
                (TypedVar (substV s x) t, substVDecisionTree s dt)
            )
            vdt
        )
    DecisionLeaf e -> DecisionLeaf (substVExpr s e)

substV :: VarSubst -> String -> String
substV (from, to) var = if var == from then to else var
