-- | Type annotated AST as a result of typechecking
module AnnotAst
    ( TVar(..)
    , TPrim(..)
    , TConst
    , Type(..)
    , Scheme(..)
    , TypedVar(..)
    , Const(..)
    , VariantIx
    , Access(..)
    , Span
    , VarBindings
    , DecisionTree(..)
    , Expr(..)
    , Defs
    , TypeDefs
    , Ctors
    , Externs
    )
where

import Data.Map.Strict (Map)
import Data.Word

import Ast (TVar(..), TPrim(..), TConst, Type(..), Scheme(..), Const(..))


data TypedVar = TypedVar String Type
    deriving (Show, Eq, Ord)

type VariantIx = Word64

data Access = Obj | As Access [Type] | Sel Word32 Access
    deriving (Show, Eq, Ord)

type Span = Int

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
    | FunMatch DecisionTree Type Type
    | Ctor VariantIx TConst [Type]
    deriving (Show)

type Defs = Map String (Scheme, Expr)
-- type TypeDefs = Map String ([TVar], [[Type]])
type TypeDefs = Map String ([TVar], [(String, [Type])])
type Ctors = Map String (VariantIx, (String, [TVar]), [Type], Span)
type Externs = Map String Type

-- data Program = Program Expr Defs TypeDefs Externs
--     deriving (Show)
