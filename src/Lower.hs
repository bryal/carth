module Lower (lower, builtinExterns) where

import Data.Bifunctor
import qualified Data.Map as Map
import Data.Map (Map)

import Misc
import qualified Monomorphic as Ast
import qualified Monomorphize
import Low


lower :: Ast.Program -> Program
lower (Ast.Program defs datas externs) =
    Program (lowerDefs defs) (lowerDatas datas) (lowerExterns externs)

builtinExterns :: Map String Type
builtinExterns = fmap lowerType Monomorphize.builtinExterns

lowerDefs :: Ast.Defs -> Defs
lowerDefs (Topo defs) = Topo $ map lowerDef defs

lowerDef :: Ast.Def -> Def
lowerDef = \case
    Ast.VarDef d -> VarDef $ lowerVarDef d
    Ast.RecDefs ds -> RecDefs $ lowerRecDefs ds

lowerVarDef :: Ast.VarDef -> VarDef
lowerVarDef = bimap lowerTypedVar (fmap (bimap (map lowerType) lowerExpr'))

lowerRecDefs :: Ast.RecDefs -> RecDefs
lowerRecDefs = map lowerFunDef

lowerFunDef :: Ast.FunDef -> FunDef
lowerFunDef = bimap lowerTypedVar (fmap (bimap (map lowerType) lowerFun))

lowerFun :: Ast.Fun -> Fun
lowerFun = bimap lowerTypedVar (bimap lowerExpr lowerType)

lowerExpr :: Ast.Expr -> Expr
lowerExpr (Ast.Expr p e) = Expr p (lowerExpr' e)

lowerExpr' :: Ast.Expr' -> Expr'
lowerExpr' = \case
    Ast.Lit c -> Lit c
    Ast.Var tv -> Var $ lowerTypedVar tv
    Ast.App f a t -> App (lowerExpr f) (lowerExpr a) (lowerType t)
    Ast.If p c a -> If (lowerExpr p) (lowerExpr c) (lowerExpr a)
    Ast.Fun f -> Fun (lowerFun f)
    Ast.Let d e -> Let (lowerDef d) (lowerExpr e)
    Ast.Match m dt t -> Match (lowerExpr m) (lowerDecisionTree dt) (lowerType t)
    Ast.Ction c -> Ction $ lowerCtion c
    Ast.Sizeof t -> Sizeof $ lowerType t
    Ast.Absurd t -> Absurd $ lowerType t

lowerDecisionTree :: Ast.DecisionTree -> DecisionTree
lowerDecisionTree = \case
    Ast.DLeaf (bs, e) -> DLeaf (map (bimap lowerTypedVar lowerAccess) bs, lowerExpr e)
    Ast.DSwitch a cs def ->
        DSwitch (lowerAccess a) (fmap lowerDecisionTree cs) (lowerDecisionTree def)
    Ast.DSwitchStr a cs def ->
        DSwitchStr (lowerAccess a) (fmap lowerDecisionTree cs) (lowerDecisionTree def)

lowerAccess :: Ast.Access -> Access
lowerAccess = fmap lowerType

lowerCtion :: Ast.Ction -> Ction
lowerCtion (i, s, tc, es) = (i, s, lowerTConst tc, map lowerExpr es)

lowerDatas :: Ast.Datas -> Datas
lowerDatas = Map.fromList . map (bimap lowerTConst (map (map lowerType))) . Map.toList

lowerExterns :: Ast.Externs -> Externs
lowerExterns = map (\(x, t, p) -> (x, lowerType t, p))

lowerTypedVar :: Ast.TypedVar -> TypedVar
lowerTypedVar (Ast.TypedVar x t) = TypedVar x (lowerType t)

lowerTConst :: Ast.TConst -> TConst
lowerTConst = second (map lowerType)

lowerType :: Ast.Type -> Type
lowerType = \case
    Ast.TPrim p -> TPrim p
    Ast.TFun a r -> TFun (lowerType a) (lowerType r)
    Ast.TBox t -> TBox (lowerType t)
    Ast.TConst tc -> TConst (lowerTConst tc)
