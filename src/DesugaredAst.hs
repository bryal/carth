module DesugaredAst
    ( TVar(..)
    , TPrim(..)
    , TConst
    , Type(..)
    , Scheme(..)
    , TypedVar(..)
    , Const(..)
    , VariantIx
    , Span
    , Access(..)
    , VarBindings
    , DecisionTree(..)
    , Expr(..)
    , Defs
    , TypeDefs
    , Externs
    , Program(..)
    , startType
    )
where

import Data.Map.Strict (Map)

import AnnotAst
    ( TVar(..)
    , TPrim(..)
    , TConst
    , Type(..)
    , Scheme(..)
    , Const(..)
    , VariantIx
    , Span
    , Access(..)
    , startType
    )

data TypedVar = TypedVar String Type
    deriving (Show, Eq, Ord)

type VarBindings = Map TypedVar Access

data DecisionTree
    = DLeaf (VarBindings, Expr)
    | DSwitch Access (Map VariantIx DecisionTree) DecisionTree
    deriving Show

data Expr
    = Lit Const
    | Var TypedVar
    | App Expr Expr Type
    | If Expr Expr Expr
    | Fun (String, Type) (Expr, Type)
    | Let Defs Expr
    | Match Expr DecisionTree Type
    | Ction VariantIx Span TConst [Expr]
    | Box Expr
    | Deref Expr
    deriving (Show)

type Defs = Map String (Scheme, Expr)
type TypeDefs = Map String ([TVar], [[Type]])
type Externs = Map String Type

data Program = Program Defs TypeDefs Externs
    deriving (Show)