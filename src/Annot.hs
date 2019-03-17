{-# LANGUAGE TemplateHaskell #-}

module Annot
    ( Program(..)
    , Expr(..)
    , Def
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

import Ast (Const(..), Id, Pat(..))
import Control.Lens (makeLenses)
import Data.Map.Strict (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import NonEmpty

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
mainType = TFun typeUnit typeInt

mainScheme :: Scheme
mainScheme = Forall Set.empty mainType

data Expr
    = Lit Const
    | Var Id
    | App Expr
          Expr
    | If Expr
         Expr
         Expr
    | Fun Id
          Expr
    | Let Defs
          Expr
    | Match Expr
            (NonEmpty (Pat, Expr))
    | FunMatch (NonEmpty (Pat, Expr))
    | Constructor String
    deriving (Show, Eq)

type Def = (Id, Expr)

type Defs = Map Id (Scheme, Expr)

data Program =
    Program Expr
            Defs
    deriving (Show)
