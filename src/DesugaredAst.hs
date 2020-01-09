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
    , Con(..)
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
import Data.Word

import AnnotAst
    ( TVar(..)
    , TPrim(..)
    , TConst
    , Type(..)
    , Scheme(..)
    , Const(..)
    , VariantIx
    , Span
    , Con(..)
    , startType
    )

data TypedVar = TypedVar String Type
    deriving (Show, Eq, Ord)

data Access
    = Obj
    | As Access Span [Type]
    | Sel Word32 Span Access
    | ADeref Access
    deriving (Show, Eq, Ord)

type VarBindings = Map TypedVar Access

data DecisionTree
    = DLeaf (VarBindings, Expr)
    | DSwitch Access (Map VariantIx DecisionTree) DecisionTree
    | DSwitchStr Access (Map String DecisionTree) DecisionTree
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
    | Absurd Type
    deriving (Show)

type Defs = Map String (Scheme, Expr)
type TypeDefs = Map String ([TVar], [[Type]])
type Externs = Map String Type

data Program = Program Defs TypeDefs Externs
    deriving (Show)
