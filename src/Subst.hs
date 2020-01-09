{-# LANGUAGE LambdaCase #-}

module Subst (Subst, subst, substTopDefs, substPat, composeSubsts) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Bifunctor
import Data.Maybe

import qualified AnnotAst as An
import AnnotAst hiding (Defs, Expr)


type Defs = An.Defs Cases
type Expr = An.Expr Cases

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
    Match e cs tp tbody ->
        Match (substExpr s e) (substCases s cs) (subst s tp) (subst s tbody)
    FunMatch cs tp tb -> FunMatch (substCases s cs) (subst s tp) (subst s tb)
    Ctor i span' (tx, tts) ps ->
        Ctor i span' (tx, map (subst s) tts) (map (subst s) ps)
    Box e -> Box (substExpr s e)
    Deref e -> Deref (substExpr s e)
    Absurd t -> Absurd (subst s t)

substCases :: Subst -> Cases -> Cases
substCases s (Cases cs) = Cases (map (bimap (substPat s) (substExpr s)) cs)

substPat :: Subst -> Pat -> Pat
substPat s (WithPos pos pat) = WithPos pos $ case pat of
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
