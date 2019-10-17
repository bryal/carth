-- | Monomorphic AST as a result of monomorphization

{-# LANGUAGE TemplateHaskell, LambdaCase, MultiParamTypeClasses
           , FlexibleInstances, FlexibleContexts #-}

module MonoAst
    ( TPrim(..)
    , TConst
    , Type(..)
    , TypedVar(..)
    , VariantIx
    , Pat(..)
    , Ctor
    , Const(..)
    , Expr(..)
    , Defs(..)
    , TypeDefs
    , Program(..)
    , mainType
    )
where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import AnnotAst (VariantIx)

import FreeVars
import Ast (Const(..), TPrim(..))

type TConst = (String, [Type])

data Type
    = TPrim TPrim
    | TFun Type Type
    | TConst TConst
    deriving (Show, Eq, Ord)

data TypedVar = TypedVar String Type
    deriving (Show, Eq, Ord)

data Pat
    = PConstruction VariantIx [Pat]
    | PVar TypedVar
    deriving (Show, Eq)

-- | (Variant index, constructed type, innter type of this variant)
type Ctor = (VariantIx, TConst, [Type])

data Expr
    = Lit Const
    | Var TypedVar
    | App Expr Expr
    | If Expr Expr Expr
    | Fun TypedVar (Expr, Type)
    | Let Defs Expr
    | Match Expr [(Pat, Expr)]
    | Ctor Ctor
    deriving (Show)

newtype Defs = Defs (Map TypedVar Expr)
    deriving (Show)

type Variant = [Type]
type TypeDefs = [(TConst, [Variant])]

data Program = Program Expr Defs TypeDefs
    deriving (Show)


instance FreeVars Expr TypedVar where
    freeVars = fvExpr

instance Pattern Pat TypedVar where
    patternBoundVars = bvPat


fvExpr :: Expr -> Set TypedVar
fvExpr = \case
    Lit _ -> Set.empty
    Var x -> Set.singleton x
    App f a -> fvApp f a
    If p c a -> fvIf p c a
    Fun p (b, _) -> fvFun p b
    Let (Defs bs) e -> fvLet (Map.keysSet bs, Map.elems bs) e
    Match e cs -> fvMatch e cs
    Ctor _ -> Set.empty

bvPat :: Pat -> Set TypedVar
bvPat = \case
    PConstruction _ ps -> Set.unions (map bvPat ps)
    PVar x -> Set.singleton x

mainType :: Type
mainType = TFun (TPrim TUnit) (TPrim TUnit)
