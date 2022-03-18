module Front.Subst (Subst, Subst', subst, subst', substDef, substExpr, substExpr', substFunMatch, substFunMatch', composeSubsts) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Bifunctor
import Data.Maybe

import Front.SrcPos
import Front.Inferred

-- | Map of substitutions from type-variables to more specific types
type Subst = TVar -> Maybe Type
type Subst' = Map TVar Type

substDef :: Subst -> Def -> Def
substDef s = \case
    VarDef d -> VarDef (second (second (substExpr' s)) d)
    RecDefs ds -> RecDefs (map (second (second (mapPosd (substFunMatch' s)))) ds)

substExpr :: Map TVar Type -> Expr -> Expr
substExpr s = substExpr' (flip Map.lookup s)

substExpr' :: Subst -> Expr -> Expr
substExpr' s (WithPos pos expr) = WithPos pos $ case expr of
    Lit c -> Lit c
    Var v -> Var (second (substTypedVar s) v)
    App f as rt -> App (substExpr' s f) (map (substExpr' s) as) (subst' s rt)
    If p c a -> If (substExpr' s p) (substExpr' s c) (substExpr' s a)
    Let def body -> Let (substDef s def) (substExpr' s body)
    FunMatch f -> FunMatch (substFunMatch' s f)
    Ctor i span' (tx, tts) ps ->
        Ctor i span' (tx, map (subst' s) tts) (map (subst' s) ps)
    Sizeof t -> Sizeof (subst' s t)

substFunMatch :: Map TVar Type -> FunMatch -> FunMatch
substFunMatch s = substFunMatch' (flip Map.lookup s)

substFunMatch' :: Subst -> FunMatch -> FunMatch
substFunMatch' s (cs, tp, tb) = ((substCases s cs), (map (subst' s) tp), (subst' s tb))

substCases :: Subst -> Cases -> Cases
substCases s cs = map (bimap (mapPosd (map (substPat s))) (substExpr' s)) cs

substPat :: Subst -> Pat -> Pat
substPat s (Pat pos t pat) = Pat pos (subst' s t) $ case pat of
    PWild -> PWild
    PVar v -> PVar (substTypedVar s v)
    PBox p -> PBox (substPat s p)
    PCon c ps -> PCon (substCon s c) (map (substPat s) ps)

substCon :: Subst -> Con -> Con
substCon s (Con ix sp ts) = Con ix sp (map (subst' s) ts)

substTypedVar :: Subst -> TypedVar -> TypedVar
substTypedVar s (TypedVar x t) = TypedVar x (subst' s t)

subst :: Map TVar Type -> Type -> Type
subst s = subst' (flip Map.lookup s)

subst' :: Subst -> Type -> Type
subst' s t = case t of
    TVar tv -> fromMaybe t (s tv)
    TPrim _ -> t
    TFun as b -> TFun (map (subst' s) as) (subst' s b)
    TBox a -> TBox (subst' s a)
    TConst (c, ts) -> TConst (c, (map (subst' s) ts))

composeSubsts :: Map TVar Type -> Map TVar Type -> Map TVar Type
composeSubsts s1 s2 = Map.union (fmap (subst s1) s2) s1
