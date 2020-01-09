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
    , Con(..)
    , Pat'(..)
    , Pat
    , Cases(..)
    , DecisionTree(..)
    , VarBindings
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

data Con = Con
    { variant :: VariantIx
    , span :: Span
    , argTs :: [Type]
    }
    deriving Show

data Pat'
    = PVar TypedVar
    | PWild
    | PCon Con [Pat]
    | PBox Pat
    deriving Show
type Pat = WithPos Pat'

newtype Cases = Cases [(Pat, Expr Cases)]
    deriving Show

data DecisionTree
    = DLeaf (VarBindings, Expr DecisionTree)
    | DSwitch Access (Map VariantIx DecisionTree) DecisionTree
    deriving Show

type VarBindings = Map TypedVar Access

data Expr' m
    = Lit Const
    | Var TypedVar
    | App (Expr m) (Expr m) Type
    | If (Expr m) (Expr m) (Expr m)
    | Let (Defs m) (Expr m)
    | Match (Expr m) m Type Type
    | FunMatch m Type Type
    | Ctor VariantIx Span TConst [Type]
    | Box (Expr m)
    | Deref (Expr m)
    deriving (Show)

type Expr m = WithPos (Expr' m)

type Defs m = Map String (Scheme, Expr m)
type TypeDefs = Map String ([TVar], [(String, [Type])])
type Ctors = Map String (VariantIx, (String, [TVar]), [Type], Span)
type Externs = Map String Type
