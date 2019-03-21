{-# LANGUAGE TemplateHaskell #-}

module Annot
    ( Program(..)
    , Expr(..)
    , Defs
    , TVar
    , Type(..)
    , Scheme(..)
    , scmParams
    , scmBody
    , typeUnit
    , typeInt
    , typeDouble
    , typeStr
    , typeBool
    , typeChar
    , mainType
    , mainScheme
    ) where

import Ast (Const(..))
import Control.Lens (makeLenses)
import Data.Map.Strict (Map)
import Data.Set (Set)
import qualified Data.Set as Set

-- Type annotated AST
type TVar = String

data Type
    = TVar TVar
    | TConst String
    | TFun Type
           Type
    deriving (Show, Eq)

typeUnit, typeInt, typeDouble, typeStr, typeBool, typeChar :: Type
typeUnit = TConst "Unit"

typeInt = TConst "Int"

typeDouble = TConst "Double"

typeChar = TConst "Char"

typeStr = TConst "Str"

typeBool = TConst "Bool"

data Scheme = Forall
    { _scmParams :: (Set TVar)
    , _scmBody :: Type
    } deriving (Show, Eq)

makeLenses ''Scheme

mainType :: Type
mainType = TFun typeUnit typeUnit

mainScheme :: Scheme
mainScheme = Forall Set.empty mainType

data Expr
    = Lit Const
    | Var String
          Type
    | App Expr
          Expr
    | If Expr
         Expr
         Expr
    | Fun (String, Type)
          Expr
    | Let Defs
          Expr
    deriving (Show, Eq)

type Defs = Map String (Scheme, Expr)

data Program =
    Program Expr
            Defs
    deriving (Show)
