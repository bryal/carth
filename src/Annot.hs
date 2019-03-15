{-# LANGUAGE TemplateHaskell #-}

module Annot
  ( Program (..)
  , Expr (..)
  , Def, Defs
  , Pat (..)
  , Id (..)
  , TVar, Type (..)
  , Scheme (..), scmParams, scmBody
  , typeUnit, typeInt, typeDouble, typeStr, typeBool, typeChar ) where

import NonEmpty
import Data.Map.Strict (Map)
import Data.String
import Data.Set
import Control.Lens

-- Type annotated AST

type TVar = String

data Type = TVar TVar
          | TConst String
          | TFun Type Type
  deriving (Show, Eq)

typeUnit, typeInt, typeDouble, typeStr, typeBool, typeChar :: Type
typeUnit = TConst "Unit"; typeInt = TConst "Int"; typeDouble = TConst "Double"
typeChar = TConst "Char"; typeStr = TConst "Str"; typeBool   = TConst "Bool";

data Scheme = Forall { _scmParams :: (Set TVar), _scmBody :: Type }
  deriving (Show, Eq)
makeLenses ''Scheme

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
type Defs = Map Id (Scheme, Expr)

data Program = Program Expr Defs
  deriving Show

instance IsString Id where
  fromString = Id
