-- | Type annotated AST as a result of typechecking

{-# LANGUAGE TemplateHaskell, LambdaCase, MultiParamTypeClasses
           , FlexibleInstances, FlexibleContexts #-}

module AnnotAst
    ( TVar(..)
    , TPrim(..)
    , Type(..)
    , Scheme(..)
    , scmParams
    , scmBody
    , TypedVar(..)
    , Pat(..)
    , Const(..)
    , Expr(..)
    , Defs(..)
    , Program(..)
    )
where

import Data.Map.Strict (Map)

import Ast
    (TVar(..), TPrim(..), Type(..), Scheme(..), scmParams, scmBody, Const(..))

data TypedVar = TypedVar String Type
    deriving (Show, Eq, Ord)

data Pat
    = PConstruction String [Pat]
    | PVar TypedVar
    deriving (Show, Eq)

data Expr
    = Lit Const
    | Var TypedVar
    | App Expr Expr
    | If Expr
         Expr
         Expr
    | Fun (String, Type)
          (Expr, Type)
    | Let Defs Expr
    | Match Expr [(Pat, Expr)]
    | Constructor String
    deriving (Show)

newtype Defs = Defs (Map String (Scheme, Expr))
    deriving (Show)

data Program = Program Expr Defs
    deriving (Show)
