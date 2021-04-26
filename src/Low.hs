{-# LANGUAGE TemplateHaskell #-}

module Low (module Low, TPrim(..), Const(..), VariantIx, Span, tUnit, Access'(..), Virt(..)) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Bifunctor

import Misc
import SrcPos
import Checked (VariantIx, Span)
import FreeVars
import Parsed (Const(..))
import TypeAst hiding (TConst)
import qualified TypeAst
import Monomorphic (Access'(..), Virt(..))

type TConst = TypeAst.TConst Type

data Type
    = TPrim TPrim
    | TFun Type Type
    | TBox Type
    | TConst TConst
    deriving (Show, Eq, Ord)

data TypedVar = TypedVar String Type
    deriving (Show, Eq, Ord)

type Access = Access' Type

type VariantTypes = [Type]

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
    | App Expr [Expr]
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

instance FreeVars Expr TypedVar where
    freeVars (Expr _ e) = fvExpr' e

instance FreeVars Expr' TypedVar where
    freeVars = fvExpr'

expr' :: Expr -> Expr'
expr' (Expr _ e) = e

fvExpr' :: Expr' -> Set TypedVar
fvExpr' = \case
    Lit _ -> Set.empty
    Var (_, x) -> Set.singleton x
    App f a -> Set.unions (map freeVars (f : a))
    If p c a -> fvIf p c a
    Fun (p, (b, _)) -> fvFun p b
    Let (VarDef (lhs, (_, WithPos _ rhs))) (Expr _ e) ->
        Set.union (freeVars rhs) (Set.delete lhs (freeVars e))
    Let (RecDefs ds) (Expr _ e) -> fvLet (unzip (map (second (Fun . unpos . snd)) ds)) e
    Match e dt _ -> Set.union (freeVars e) (fvDecisionTree dt)
    Ction (_, _, _, as) -> Set.unions (map freeVars as)
    Sizeof _t -> Set.empty
    Absurd _ -> Set.empty

fvDecisionTree :: DecisionTree -> Set TypedVar
fvDecisionTree = \case
    DLeaf (bs, e) -> Set.difference (freeVars e) (Set.fromList (map fst bs))
    DSwitch _ cs def -> fvDSwitch (Map.elems cs) def
    DSwitchStr _ cs def -> fvDSwitch (Map.elems cs) def
    where fvDSwitch es def = Set.unions $ fvDecisionTree def : map fvDecisionTree es

defToVarDefs :: Def -> [(TypedVar, (Inst, WithPos Expr'))]
defToVarDefs = \case
    VarDef d -> [d]
    RecDefs ds -> map (second (second (mapPosd Fun))) ds
