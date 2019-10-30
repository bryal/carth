{-# LANGUAGE LambdaCase #-}

module Subst (Subst, subst, substProgram, substPat, composeSubsts) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Bifunctor
import Data.Maybe

import Match
import AnnotAst

-- | Map of substitutions from type-variables to more specific types
type Subst = Map TVar Type

substProgram :: Subst -> Program -> Program
substProgram s (Program main (Defs defs) tdefs externs) =
    Program (substExpr s main) (Defs (fmap (substDef s) defs)) tdefs externs

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
    DSwitch obj cs def -> DSwitch
        (substAccess s obj)
        (fmap (substDecisionTree s) cs)
        (substDecisionTree s def)
    DLeaf e -> DLeaf (second (substExpr s) e)

substAccess :: Subst -> Access -> Access
substAccess s = \case
    Obj -> Obj
    As a ts -> As (substAccess s a) (map (subst s) ts)
    Sel i a -> Sel i (substAccess s a)

substPat :: Subst -> Pat -> Pat
substPat s = \case
    PVar (TypedVar x t) -> PVar (TypedVar x (subst s t))
    PCon c ps -> PCon (substCon s c) (map (substPat s) ps)

substCon :: Subst -> Con -> Con
substCon s (Con ix sp ts) = Con ix sp (map (subst s) ts)

subst :: Subst -> Type -> Type
subst s t = case t of
    TVar tv -> fromMaybe t (Map.lookup tv s)
    TPrim _ -> t
    TFun a b -> TFun (subst s a) (subst s b)
    TConst (c, ts) -> TConst (c, (map (subst s) ts))

composeSubsts :: Subst -> Subst -> Subst
composeSubsts s1 s2 = Map.union (fmap (subst s1) s2) s1
