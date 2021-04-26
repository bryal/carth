{-# LANGUAGE TemplateHaskell #-}

-- | Monomorphic AST as a result of monomorphization
module Monomorphic
    ( module Monomorphic
    , TPrim(..)
    , Const(..)
    , VariantIx
    , Span
    , tUnit
    , Virt (..)
    )
where

import Data.Map (Map)
import Data.Word

import Misc
import SrcPos
import Checked (VariantIx, Span, Virt (..))
import Parsed (Const(..))
import TypeAst hiding (TConst)
import qualified TypeAst

type TConst = TypeAst.TConst Type

data Type
    = TPrim TPrim
    | TFun Type Type
    | TBox Type
    | TConst TConst
    deriving (Show, Eq, Ord)

data TypedVar = TypedVar String Type
    deriving (Show, Eq, Ord)

type VariantTypes = [Type]

data Access' t
    = Obj
    | As (Access' t) Span [t]
    | Sel Word32 Span (Access' t)
    | ADeref (Access' t)
    deriving (Show, Eq, Ord)

type Access = Access' Type

type VarBindings = [(TypedVar, Access)]

data DecisionTree
    = DLeaf (VarBindings, Expr)
    | DSwitch Access (Map VariantIx DecisionTree) DecisionTree
    | DSwitchStr Access (Map String DecisionTree) DecisionTree
    deriving Show

type Ction = (VariantIx, Span, TConst, [Expr])
type Fun = (TypedVar, (Expr, Type))

type Var = (Virt, TypedVar)

data Expr'
    = Lit Const
    | Var Var
    | App Expr Expr
    | If Expr Expr Expr
    | Fun Fun
    | Let Def Expr
    | Match Expr DecisionTree Type
    | Ction Ction
    | Sizeof Type
    | Absurd Type
    deriving (Show)

data Expr = Expr (Maybe SrcPos) Expr'
    deriving Show

type Defs = TopologicalOrder Def
data Def = VarDef VarDef | RecDefs RecDefs deriving Show
type Inst = [Type]
type VarDef = (TypedVar, (Inst, WithPos Expr'))
type RecDefs = [FunDef]
type FunDef = (TypedVar, (Inst, WithPos Fun))
type Datas = Map TConst [VariantTypes]
type Externs = [(String, Type, SrcPos)]

data Program = Program Defs Datas Externs
    deriving Show

instance TypeAst Type where
    tprim = TPrim
    tconst = TConst
    tfun = TFun
    tbox = TBox

instance Functor Access' where
    fmap f = \case
        Obj -> Obj
        As a s ts -> As (fmap f a) s (map f ts)
        Sel i s a -> Sel i s (fmap f a)
        ADeref a -> ADeref (fmap f a)

expr' :: Expr -> Expr'
expr' (Expr _ e) = e
