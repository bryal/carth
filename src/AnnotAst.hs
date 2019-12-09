-- | Type annotated AST as a result of typechecking

{-# LANGUAGE TemplateHaskell, LambdaCase, MultiParamTypeClasses
           , FlexibleInstances, FlexibleContexts #-}

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
    , VarBindings
    , DecisionTree(..)
    , Ction
    , Expr(..)
    , Defs(..)
    , TypeDefs
    , Externs
    , Program(..)
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

type VarBindings = Map TypedVar Access

data DecisionTree
    = DLeaf (VarBindings, Expr)
    | DSwitch Access (Map VariantIx DecisionTree) DecisionTree
    deriving Show

type Ction = (VariantIx, (String, [Type]), [Expr])

data Expr
    = Lit Const
    | Var TypedVar
    | App Expr Expr Type
    | If Expr Expr Expr
    | Fun (String, Type) (Expr, Type)
    | Let Defs Expr
    | Match Expr DecisionTree Type
    | Ction Ction
    deriving (Show)

newtype Defs = Defs (Map String (Scheme, Expr))
    deriving (Show)

type TypeDefs = Map String ([TVar], [[Type]])

type Externs = Map String Type

data Program = Program Expr Defs TypeDefs Externs
    deriving (Show)
