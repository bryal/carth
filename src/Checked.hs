module Checked
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
    , Expr'(..)
    , Expr(..)
    , withPos
    , noPos
    , Defs
    , TypeDefs
    , Externs
    , Program(..)
    , mainType
    )
where

import Data.Map.Strict (Map)
import Data.Word

import Misc
import SrcPos
import Inferred
    ( TVar(..)
    , TPrim(..)
    , TConst
    , Type(..)
    , Scheme(..)
    , Const(..)
    , VariantIx
    , Span
    , Con(..)
    , mainType
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

data Expr'
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

data Expr = Expr (Maybe SrcPos) Expr'
    deriving (Show)

withPos :: SrcPos -> Expr' -> Expr
withPos = Expr . Just

noPos :: Expr' -> Expr
noPos = Checked.Expr Nothing

type Defs = TopologicalOrder (String, (WithPos (Scheme, Expr)))
type TypeDefs = Map String ([TVar], [[Type]])
type Externs = Map String (Type, SrcPos)

data Program = Program Defs TypeDefs Externs
    deriving (Show)
