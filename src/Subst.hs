{-# LANGUAGE LambdaCase #-}

module Subst (Subst, subst, substTopDefs, substPat, composeSubsts) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Bifunctor
import Data.Maybe

import Match
import AnnotAst

-- | Map of substitutions from type-variables to more specific types
type Subst = Map TVar Type

substTopDefs :: Subst -> Defs -> Defs
substTopDefs s defs = fmap (substDef s) defs

substDef :: Subst -> (Scheme, Expr) -> (Scheme, Expr)
substDef s = second (substExpr s)

substExpr :: Subst -> Expr -> Expr
substExpr s (WithPos p e) = WithPos p $ case e of
    Lit c -> Lit c
    Var v -> Var (substTypedVar s v)
    App f a rt -> App (substExpr s f) (substExpr s a) (subst s rt)
    If p c a -> If (substExpr s p) (substExpr s c) (substExpr s a)
    Let defs body -> Let (fmap (substDef s) defs) (substExpr s body)
    Match e dt tbody ->
        Match (substExpr s e) (substDecisionTree s dt) (subst s tbody)
    FunMatch dt tp tb ->
        FunMatch (substDecisionTree s dt) (subst s tp) (subst s tb)
    Ctor i span' (tx, tts) ps ->
        Ctor i span' (tx, map (subst s) tts) (map (subst s) ps)
    Box e -> Box (substExpr s e)
    Deref e -> Deref (substExpr s e)

substDecisionTree :: Subst -> DecisionTree -> DecisionTree
substDecisionTree s = \case
    DSwitch obj cs def -> DSwitch
        (substAccess s obj)
        (fmap (substDecisionTree s) cs)
        (substDecisionTree s def)
    DLeaf (bs, e) -> DLeaf
        ( Map.fromList
            (map (bimap (substTypedVar s) (substAccess s)) (Map.toList bs))
        , substExpr s e
        )

substAccess :: Subst -> Access -> Access
substAccess s = \case
    Obj -> Obj
    As a span' ts -> As (substAccess s a) span' (map (subst s) ts)
    Sel i span' a -> Sel i span' (substAccess s a)
    ADeref a -> ADeref (substAccess s a)

substPat :: Subst -> Pat -> Pat
substPat s = \case
    PWild -> PWild
    PVar v -> PVar (substTypedVar s v)
    PBox p -> PBox (substPat s p)
    PCon c ps -> PCon (substCon s c) (map (substPat s) ps)

substCon :: Subst -> Con -> Con
substCon s (Con ix sp ts) = Con ix sp (map (subst s) ts)

substTypedVar :: Subst -> TypedVar -> TypedVar
substTypedVar s (TypedVar x t) = TypedVar x (subst s t)

subst :: Subst -> Type -> Type
subst s t = case t of
    TVar tv -> fromMaybe t (Map.lookup tv s)
    TPrim _ -> t
    TFun a b -> TFun (subst s a) (subst s b)
    TBox a -> TBox (subst s a)
    TConst (c, ts) -> TConst (c, (map (subst s) ts))

composeSubsts :: Subst -> Subst -> Subst
composeSubsts s1 s2 = Map.union (fmap (subst s1) s2) s1
