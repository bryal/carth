-- | Monomorphic AST as a result of monomorphization

{-# LANGUAGE TemplateHaskell, LambdaCase, MultiParamTypeClasses
           , FlexibleInstances, FlexibleContexts #-}

module MonoAst
    ( TPrim(..)
    , TConst
    , Type(..)
    , TypedVar(..)
    , Const(..)
    , VariantIx
    , VariantTypes
    , Access(..)
    , VarBindings
    , DecisionTree(..)
    , Ction
    , Expr(..)
    , Defs(..)
    , TypeDefs
    , Program(..)
    , mainType
    )
where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Word

import AnnotAst (VariantIx)
import FreeVars
import Ast (Const(..), TPrim(..))

type TConst = (String, [Type])

data Type
    = TPrim TPrim
    | TFun Type Type
    | TConst TConst
    deriving (Show, Eq, Ord)

data TypedVar = TypedVar String Type
    deriving (Show, Eq, Ord)

type VariantTypes = [Type]

data Access = Obj | As Access [Type] | Sel Word32 Access
    deriving (Show, Eq, Ord)

type VarBindings = [(TypedVar, Access)]

data DecisionTree
    = DLeaf (VarBindings, Expr)
    | DSwitch Access (Map VariantIx DecisionTree) DecisionTree
    deriving Show

type Ction = (VariantIx, TConst, [Expr])

data Expr
    = Lit Const
    | Var TypedVar
    | App Expr Expr
    | If Expr Expr Expr
    | Fun TypedVar (Expr, Type)
    | Let Defs Expr
    | Match Expr DecisionTree Type
    | Ction Ction
    deriving (Show)

newtype Defs = Defs (Map TypedVar Expr)
    deriving (Show)

type TypeDefs = [(TConst, [VariantTypes])]

type Externs = [(String, Type)]

data Program = Program Expr Defs TypeDefs Externs
    deriving (Show)


instance FreeVars Expr TypedVar where
    freeVars = fvExpr


fvExpr :: Expr -> Set TypedVar
fvExpr = \case
    Lit _ -> Set.empty
    Var x -> Set.singleton x
    App f a -> fvApp f a
    If p c a -> fvIf p c a
    Fun p (b, _) -> fvFun p b
    Let (Defs bs) e -> fvLet (Map.keysSet bs, Map.elems bs) e
    Match e dt _ -> Set.union (fvExpr e) (fvDecisionTree dt)
    Ction (_, _, as) -> Set.unions (map fvExpr as)

fvDecisionTree :: DecisionTree -> Set TypedVar
fvDecisionTree = \case
    DSwitch _ cs def ->
        Set.unions $ fvDecisionTree def : map fvDecisionTree (Map.elems cs)
    DLeaf (bs, e) -> Set.difference (fvExpr e) (Set.fromList (map fst bs))

mainType :: Type
mainType = TFun (TPrim TUnit) (TPrim TUnit)
