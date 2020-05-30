{-# LANGUAGE TemplateHaskell, LambdaCase, MultiParamTypeClasses
           , FlexibleInstances, FlexibleContexts #-}

-- | Monomorphic AST as a result of monomorphization
module Monomorphic (module Monomorphic, TPrim(..), Const(..), VariantIx, Span, tUnit) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Word
import Data.Bifunctor

import Misc
import SrcPos
import Checked (VariantIx, Span)
import FreeVars
import Parsed (Const(..), TPrim(..), tUnit)

type TConst = (String, [Type])

data Type
    = TPrim TPrim
    | TFun Type Type
    | TBox Type
    | TConst TConst
    deriving (Show, Eq, Ord)

data TypedVar = TypedVar String Type
    deriving (Show, Eq, Ord)

type VariantTypes = [Type]

data Access
    = Obj
    | As Access Span [Type]
    | Sel Word32 Span Access
    | ADeref Access
    deriving (Show, Eq, Ord)

type VarBindings = [(TypedVar, Access)]

data DecisionTree
    = DLeaf (VarBindings, Expr)
    | DSwitch Access (Map VariantIx DecisionTree) DecisionTree
    | DSwitchStr Access (Map String DecisionTree) DecisionTree
    deriving Show

type Ction = (VariantIx, Span, TConst, [Expr])
type Fun = (TypedVar, (Expr, Type))

data Expr'
    = Lit Const
    | Var TypedVar
    | App Expr Expr Type
    | If Expr Expr Expr
    | Fun Fun
    | Let Def Expr
    | Match Expr DecisionTree Type
    | Ction Ction
    | Sizeof Type
    | Deref Expr
    | Store Expr Expr
    | Absurd Type
    | Transmute SrcPos Expr Type Type
    deriving (Show)

data Expr = Expr (Maybe SrcPos) Expr'
    deriving (Show)

type Defs = TopologicalOrder Def
data Def = VarDef VarDef | RecDefs RecDefs deriving Show
type VarDef = (TypedVar, WithPos ([Type], Expr'))
type RecDefs = [FunDef]
type FunDef = (TypedVar, WithPos ([Type], Fun))
type TypeDefs = [(TConst, [VariantTypes])]
type Externs = [(String, Type, SrcPos)]

data Program = Program Defs TypeDefs Externs
    deriving (Show)


instance FreeVars Expr TypedVar where
    freeVars (Expr _ e) = fvExpr' e

instance FreeVars Expr' TypedVar where
    freeVars = fvExpr'


expr' :: Expr -> Expr'
expr' (Expr _ e) = e

fvExpr' :: Expr' -> Set TypedVar
fvExpr' = \case
    Lit _ -> Set.empty
    Var x -> Set.singleton x
    App f a _ -> fvApp f a
    If p c a -> fvIf p c a
    Fun (p, (b, _)) -> fvFun p b
    Let d (Expr _ e) ->
        let bs = defToVarDefs d in fvLet (unzip (map (second (snd . unpos)) bs)) e
    Match e dt _ -> Set.union (freeVars e) (fvDecisionTree dt)
    Ction (_, _, _, as) -> Set.unions (map freeVars as)
    Sizeof _t -> Set.empty
    Deref e -> freeVars e
    Store x p -> Set.union (freeVars x) (freeVars p)
    Absurd _ -> Set.empty
    Transmute _ x _ _ -> freeVars x

fvDecisionTree :: DecisionTree -> Set TypedVar
fvDecisionTree = \case
    DLeaf (bs, e) -> Set.difference (freeVars e) (Set.fromList (map fst bs))
    DSwitch _ cs def -> fvDSwitch (Map.elems cs) def
    DSwitchStr _ cs def -> fvDSwitch (Map.elems cs) def
    where fvDSwitch es def = Set.unions $ fvDecisionTree def : map fvDecisionTree es

defToVarDefs :: Def -> [(TypedVar, WithPos ([Type], Expr'))]
defToVarDefs = \case
    VarDef d -> [d]
    RecDefs ds -> map (second (mapPosd (second Fun))) ds

funDefFromVarDef :: VarDef -> (TypedVar, WithPos ([Type], Fun))
funDefFromVarDef = second $ mapPosd $ second $ \case
    Fun f -> f
    e -> ice $ "funDefFromVarDef on non-positioned function " ++ show e

mainType :: Type
mainType = TFun (TConst tUnit) (TConst tUnit)
