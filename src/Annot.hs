{-# LANGUAGE TemplateHaskell #-}

module Annot
    ( Program(..)
    , Expr(..)
    , Type(..)
    , typeUnit
    , typeInt
    , typeDouble
    , typeStr
    , typeBool
    , typeChar
    , mainType
    ) where

import Ast (Const(..))

class Type t where
    tConst :: String -> t
    tFun :: t -> t -> t

typeUnit, typeInt, typeDouble, typeStr, typeBool, typeChar :: Type t => t
typeUnit = tConst "Unit"

typeInt = tConst "Int"

typeDouble = tConst "Double"

typeChar = tConst "Char"

typeStr = tConst "Str"

typeBool = tConst "Bool"

mainType :: Type t => t
mainType = tFun typeUnit typeUnit

data Expr t ds
    = Lit Const
    | Var String
          t
    | App (Expr t ds)
          (Expr t ds)
    | If (Expr t ds)
         (Expr t ds)
         (Expr t ds)
    | Fun (String, t)
          (Expr t ds)
    | Let ds
          (Expr t ds)
    deriving (Show, Eq)

data Program t ds =
    Program (Expr t ds)
            ds
    deriving (Show)
