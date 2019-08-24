-- | Monomorphic AST as a result of monomorphization

{-# LANGUAGE TemplateHaskell, LambdaCase, MultiParamTypeClasses
           , FlexibleInstances, FlexibleContexts #-}

module MonoAst
    ( TPrim(..)
    , Type(..)
    , TypedVar(..)
    , Const(..)
    , Expr(..)
    , Defs(..)
    , Program(..)
    , mainType
    )
where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Set (Set)

import FreeVars
import Ast (Const(..), TPrim(..))

data Type
    = TPrim TPrim
    | TFun Type
           Type
    | TConst String [Type]
    deriving (Show, Eq, Ord)

data TypedVar = TypedVar String Type
    deriving (Show, Eq, Ord)

data Expr
    = Lit Const
    | Var TypedVar
    | App Expr
          Expr
    | If Expr
         Expr
         Expr
    | Fun TypedVar
          (Expr, Type)
    | Let Defs
          Expr
    deriving (Show)

newtype Defs = Defs (Map TypedVar Expr)
    deriving (Show)

data Program = Program Expr Defs
    deriving (Show)

mainType :: Type
mainType = TFun (TPrim TUnit) (TPrim TUnit)

instance FreeVars Expr TypedVar where
    freeVars = fvExpr

fvExpr :: Expr -> Set TypedVar
fvExpr = \case
    Lit c -> fvLit c
    Var x -> fvVar x
    App f a -> fvApp f a
    If p c a -> fvIf p c a
    Fun p (b, _) -> fvFun p b
    Let (Defs bs) e -> fvLet (Map.keysSet bs, Map.elems bs) e
