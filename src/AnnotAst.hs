-- | Type annotated AST as a result of typechecking
module AnnotAst
    ( WithPos(..)
    , TVar(..)
    , TPrim(..)
    , TConst
    , Type(..)
    , Scheme(..)
    , Id
    , TypedVar(..)
    , Const(..)
    , VariantIx
    , Access(..)
    , Span
    , VarBindings
    , DecisionTree(..)
    , Expr
    , Expr'(..)
    , Defs
    , TypeDefs
    , Ctors
    , Externs
    , startType
    )
where

import Data.Map.Strict (Map)
import Data.Word

import Ast
    (TVar(..), TPrim(..), TConst, Type(..), Scheme(..), Const(..), startType)
import SrcPos


type Id = WithPos String

data TypedVar = TypedVar Id Type
    deriving (Show, Eq, Ord)

type VariantIx = Integer

data Access
    = Obj
    | As Access Span [Type]
    | Sel Word32 Span Access
    | ADeref Access
    deriving (Show, Eq, Ord)

type Span = Integer

type VarBindings = Map TypedVar Access

data DecisionTree
    = DLeaf (VarBindings, Expr)
    | DSwitch Access (Map VariantIx DecisionTree) DecisionTree
    deriving Show

data Expr'
    = Lit Const
    | Var TypedVar
    | App Expr Expr Type
    | If Expr Expr Expr
    | Fun (String, Type) (Expr, Type)
    | Let Defs Expr
    | Match Expr DecisionTree Type
    | FunMatch DecisionTree Type Type
    | Ctor VariantIx Span TConst [Type]
    | Box Expr
    | Deref Expr
    deriving (Show)

type Expr = WithPos Expr'

type Defs = Map String (Scheme, Expr)
type TypeDefs = Map String ([TVar], [(String, [Type])])
type Ctors = Map String (VariantIx, (String, [TVar]), [Type], Span)
type Externs = Map String Type
