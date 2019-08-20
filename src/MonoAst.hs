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
import qualified Data.Set as Set
import Data.Set (Set)

import Misc
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
    Lit _ -> Set.empty
    Var x -> Set.singleton x
    App f a -> Set.unions (map freeVars [f, a])
    If p c a -> Set.unions (map freeVars [p, c, a])
    Fun p (b, _) -> Set.delete p (freeVars b)
    Let (Defs bs) e -> Set.difference
        (Set.union (freeVars e) (Set.unions (map fvExpr (Map.elems bs))))
        (Map.keysSet bs)
