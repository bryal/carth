{-# LANGUAGE LambdaCase #-}

module Subst (Subst, subst, substTopDefs, substPat, composeSubsts) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Bifunctor
import Data.Maybe

import Misc
import SrcPos
import Inferred


-- | Map of substitutions from type-variables to more specific types
type Subst = Map TVar Type

substTopDefs :: Subst -> Defs -> Defs
substTopDefs s (Topo defs) = Topo (map (substDef s) defs)

substDef :: Subst -> Def -> Def
substDef s = \case
    VarDef d -> VarDef (second (mapPosd (second (substExpr s))) d)
    RecDefs ds ->
        RecDefs (map (second (mapPosd (second (mapPosd (substFunMatch s))))) ds)

substExpr :: Subst -> Expr -> Expr
substExpr s (WithPos pos expr) = WithPos pos $ case expr of
    Lit c -> Lit c
    Var v -> Var (substTypedVar s v)
    App f a rt -> App (substExpr s f) (substExpr s a) (subst s rt)
    If p c a -> If (substExpr s p) (substExpr s c) (substExpr s a)
    Let def body -> Let (substDef s def) (substExpr s body)
    FunMatch f -> FunMatch (substFunMatch s f)
    Ctor i span' (tx, tts) ps -> Ctor i span' (tx, map (subst s) tts) (map (subst s) ps)
    Sizeof t -> Sizeof (subst s t)
    Deref e -> Deref (substExpr s e)
    Store x p -> Store (substExpr s x) (substExpr s p)

substFunMatch :: Subst -> FunMatch -> FunMatch
substFunMatch s (cs, tp, tb) = ((substCases s cs), (subst s tp), (subst s tb))

substCases :: Subst -> Cases -> Cases
substCases s cs = map (bimap (substPat s) (substExpr s)) cs

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
