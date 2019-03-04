module Annot (Program (..), Expr (..), Def, Defs, Pat (..), Id (..), Type, Scheme (..)) where

import NonEmpty
import Data.Map.Strict (Map)
import Data.String

-- Type annotated AST

data Type

data Scheme = Scheme [String] Type

newtype Id = Id String
  deriving (Show, Eq, Ord)

data Pat
  = PConstructor String
  | PConstruction String (NonEmpty Pat)
  | PVar Id
  deriving (Show, Eq)

data Expr
  = Unit
  | Int Int
  | Double Double
  | Str String
  | Bool Bool
  | Var Id
  | App Expr Expr
  | If Expr Expr Expr
  | Fun Id Expr
  | Let Defs Expr
  | Match Expr (NonEmpty (Pat, Expr))
  | FunMatch (NonEmpty (Pat, Expr))
  | Constructor String
  | Char Char
  deriving (Show, Eq)

type Def = (Id, Expr)
type Defs = Map Id Expr

data Program = Program Expr Defs

instance IsString Id where
  fromString = Id
