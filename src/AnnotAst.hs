{-# LANGUAGE LambdaCase #-}

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
    , Variant(..)
    , Span
    , Con(..)
    , Pat'(..)
    , Pat
    , Cases
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

import Ast
    (TVar(..), TPrim(..), TConst, Type(..), Scheme(..), Const(..), startType)
import SrcPos


type Id = WithPos String

data TypedVar = TypedVar Id Type
    deriving (Show, Eq, Ord)

type VariantIx = Integer

type Span = Integer

data Variant = VariantIx VariantIx | VariantStr String
    deriving (Show, Eq, Ord)

data Con = Con
    { variant :: Variant
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

type Cases = [(Pat, Expr)]

data Expr'
    = Lit Const
    | Var TypedVar
    | App Expr Expr Type
    | If Expr Expr Expr
    | Let Defs Expr
    | FunMatch Cases Type Type
    | Ctor VariantIx Span TConst [Type]
    | Box Expr
    | Deref Expr
    deriving Show

type Expr = WithPos Expr'

type Defs = Map String (Scheme, Expr)
type TypeDefs = Map String ([TVar], [(String, [Type])])
type Ctors = Map String (VariantIx, (String, [TVar]), [Type], Span)
type Externs = Map String Type


instance Eq Con where
    (==) (Con c1 _ _) (Con c2 _ _) = c1 == c2

instance Ord Con where
    compare (Con c1 _ _) (Con c2 _ _) = compare c1 c2
