-- | Monomorphic AST as a result of monomorphization

{-# LANGUAGE TemplateHaskell, LambdaCase, MultiParamTypeClasses
           , FlexibleInstances, FlexibleContexts #-}

module MonoAst
    ( TPrim(..)
    , TConst
    , Type(..)
    , TypedVar(..)
    , Const(..)
    , VariantIx
    , VariantTypes
    , DecisionTree(..)
    , Ction
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

type VariantTypes = [Type]

data DecisionTree
    = DecisionTree (Map VariantIx (VariantTypes, DecisionTree))
                   (Maybe (TypedVar, DecisionTree))
    | DecisionLeaf Expr
    deriving (Show)

-- | (Variant index, constructed type, arguments)
type Ction = (VariantIx, TConst, [Expr])

data Expr
    = Lit Const
    | Var TypedVar
    | App Expr Expr
    | If Expr Expr Expr
    | Fun TypedVar (Expr, Type)
    | Let Defs Expr
    | Match Expr DecisionTree Type
    | Ction Ction
    deriving (Show)

newtype Defs = Defs (Map TypedVar Expr)
    deriving (Show)

type TypeDefs = [(TConst, [VariantTypes])]

data Program = Program Expr Defs TypeDefs
    deriving (Show)


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
    Match e dt _ -> Set.union (fvExpr e) (fvDecisionTree dt)
    Ction (_, _, as) -> Set.unions (map fvExpr as)

fvDecisionTree :: DecisionTree -> Set TypedVar
fvDecisionTree = \case
    DecisionTree cs vdt ->
        Set.unions
            $ maybe Set.empty (\(v, dt) -> Set.delete v (fvDecisionTree dt)) vdt
            : map (fvDecisionTree . snd) (Map.elems cs)
    DecisionLeaf e -> fvExpr e

mainType :: Type
mainType = TFun (TPrim TUnit) (TPrim TUnit)
