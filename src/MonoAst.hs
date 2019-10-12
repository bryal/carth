-- | Monomorphic AST as a result of monomorphization

{-# LANGUAGE TemplateHaskell, LambdaCase, MultiParamTypeClasses
           , FlexibleInstances, FlexibleContexts #-}

module MonoAst
    ( TPrim(..)
    , Type(..)
    , TypedVar(..)
    , Pat(..)
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

import FreeVars
import Ast (Const(..), TPrim(..))

data Type
    = TPrim TPrim
    | TFun Type Type
    | TConst String [Type]
    deriving (Show, Eq, Ord)

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
    | If Expr Expr Expr
    | Fun TypedVar (Expr, Type)
    | Let Defs Expr
    | Match Expr [(Pat, Expr)]
    | Constructor String
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
    App f a -> fvApp f a
    If p c a -> fvIf p c a
    Fun p (b, _) -> fvFun p b
    Let (Defs bs) e -> fvLet (Map.keysSet bs, Map.elems bs) e
    Match e cs -> fvMatch e cs
    Constructor _ -> Set.empty

instance Pattern Pat TypedVar where
    patternBoundVars = bvPat

bvPat :: Pat -> Set TypedVar
bvPat = \case
    PConstruction _ ps -> Set.unions (map bvPat ps)
    PVar x -> Set.singleton x
