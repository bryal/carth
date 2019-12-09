module DesugaredAst
    ( TVar(..)
    , TPrim(..)
    , TConst
    , Type(..)
    , Scheme(..)
    , TypedVar(..)
    , Const(..)
    , VariantIx
    , Access(..)
    , VarBindings
    , DecisionTree(..)
    , Expr(..)
    , Defs
    , TypeDefs
    , Externs
    , Program(..)
    )
where

import Data.Map.Strict (Map)

import AnnotAst
    ( TVar(..)
    , TPrim(..)
    , TConst
    , Type(..)
    , TypedVar(..)
    , Scheme(..)
    , Const(..)
    , VariantIx
    , Access(..)
    , VarBindings
    )

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
    | Ction VariantIx TConst [Expr]
    deriving (Show)

type Defs = Map String (Scheme, Expr)
type TypeDefs = Map String ([TVar], [[Type]])
type Externs = Map String Type

data Program = Program Expr Defs TypeDefs Externs
    deriving (Show)
