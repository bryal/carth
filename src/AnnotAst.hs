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
    , DecisionTree(..)
    , Ction
    , Expr(..)
    , Defs(..)
    , TypeDefs
    , Program(..)
    )
where

import Data.Map.Strict (Map)
import Data.Word

import Ast (TVar(..), TPrim(..), TConst, Type(..), Scheme(..), Const(..))


data TypedVar = TypedVar String Type
    deriving (Show, Eq, Ord)

type VariantIx = Word64

data DecisionTree
    = DecisionTree (Map VariantIx ([Type], DecisionTree))
                   (Maybe (TypedVar, DecisionTree))
    | DecisionLeaf Expr
    deriving (Show)

type Ction = (VariantIx, (String, [Type]), [Expr])

data Expr
    = Lit Const
    | Var TypedVar
    | App Expr Expr
    | If Expr Expr Expr
    | Fun (String, Type) (Expr, Type)
    | Let Defs Expr
    | Match Expr DecisionTree Type
    | Ction Ction
    deriving (Show)

newtype Defs = Defs (Map String (Scheme, Expr))
    deriving (Show)

type TypeDefs = Map String ([TVar], [[Type]])

data Program = Program Expr Defs TypeDefs
    deriving (Show)
