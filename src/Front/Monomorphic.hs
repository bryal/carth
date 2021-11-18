{-# LANGUAGE TemplateHaskell #-}

-- | Monomorphic AST as a result of monomorphization
module Front.Monomorphic
    ( module Front.Monomorphic
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
import Front.Checked (VariantIx, Span, Virt (..))
import Front.Parsed (Const(..))
import Front.TypeAst hiding (TConst)
import qualified Front.TypeAst as TypeAst

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
    | DSwitch Span Access (Map VariantIx DecisionTree) DecisionTree
    | DSwitchStr Access (Map String DecisionTree) DecisionTree
    deriving Show

type Ction = (VariantIx, Span, TConst, [Expr])
type Fun = (TypedVar, (Expr, Type))

type Var = (Virt, TypedVar)

data Expr
    = Lit Const
    | Var Var
    | App Expr Expr
    | If Expr Expr Expr
    | Fun Fun
    | Let Def Expr
    | Match Expr DecisionTree
    | Ction Ction
    | Sizeof Type
    | Absurd Type
    deriving (Show)

type Defs = TopologicalOrder Def
data Def = VarDef VarDef | RecDefs RecDefs deriving Show
type Inst = [Type]
type VarDef = (TypedVar, (Inst, Expr))
type RecDefs = [FunDef]
type FunDef = (TypedVar, (Inst, Fun))
type Datas = Map TConst [(String, VariantTypes)]
type Externs = [(String, [Type], Type)]

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
