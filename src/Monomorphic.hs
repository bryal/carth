-- | Monomorphic AST as a result of monomorphization

{-# LANGUAGE TemplateHaskell, LambdaCase, MultiParamTypeClasses
           , FlexibleInstances, FlexibleContexts #-}

module Monomorphic
    ( TPrim(..)
    , TConst
    , Type(..)
    , TypedVar(..)
    , Const(..)
    , VariantIx
    , VariantTypes
    , Span
    , Access(..)
    , VarBindings
    , DecisionTree(..)
    , Ction
    , Expr'(..)
    , Expr(..)
    , Defs
    , TypeDefs
    , Program(..)
    , startType
    )
where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Word

import SrcPos
import Checked (VariantIx, Span)
import FreeVars
import Parsed (Const(..), TPrim(..))

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

data Expr'
    = Lit Const
    | Var TypedVar
    | App Expr Expr Type
    | If Expr Expr Expr
    | Fun TypedVar (Expr, Type)
    | Let Defs Expr
    | Match Expr DecisionTree Type
    | Ction Ction
    | Box Expr
    | Deref Expr
    | Absurd Type
    deriving (Show)

data Expr = Expr (Maybe SrcPos) Expr'
    deriving (Show)

type Defs = Map TypedVar ([Type], Expr)
type TypeDefs = [(TConst, [VariantTypes])]
type Externs = [(String, Type)]

data Program = Program Defs TypeDefs Externs
    deriving (Show)


instance FreeVars Expr TypedVar where
    freeVars = fvExpr


fvExpr :: Expr -> Set TypedVar
fvExpr (Expr _ ex) = case ex of
    Lit _ -> Set.empty
    Var x -> Set.singleton x
    App f a _ -> fvApp f a
    If p c a -> fvIf p c a
    Fun p (b, _) -> fvFun p b
    Let bs e -> fvLet (Map.keysSet bs, map snd (Map.elems bs)) e
    Match e dt _ -> Set.union (fvExpr e) (fvDecisionTree dt)
    Ction (_, _, _, as) -> Set.unions (map fvExpr as)
    Box e -> fvExpr e
    Deref e -> fvExpr e
    Absurd _ -> Set.empty

fvDecisionTree :: DecisionTree -> Set TypedVar
fvDecisionTree = \case
    DLeaf (bs, e) -> Set.difference (fvExpr e) (Set.fromList (map fst bs))
    DSwitch _ cs def -> fvDSwitch (Map.elems cs) def
    DSwitchStr _ cs def -> fvDSwitch (Map.elems cs) def
  where
    fvDSwitch es def =
        Set.unions $ fvDecisionTree def : map fvDecisionTree es

startType :: Type
startType = TFun (TPrim TUnit) (TPrim TUnit)
