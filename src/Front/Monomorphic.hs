-- | Monomorphic AST as a result of monomorphization
module Front.Monomorphic
    ( module Front.Monomorphic
    , TPrim(..)
    , Const(..)
    , VariantIx
    , Virt (..)
    , Span
    , tUnit
    , Access' (..)
    )
where

import Data.Bifunctor
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import FreeVars
import Misc
import Front.Checked (VariantIx, Span, Access' (..), Virt (..))
import Front.Parsed (Const(..))
import Front.TypeAst hiding (TConst)
import qualified Front.TypeAst as TypeAst

type TConst = TypeAst.TConst Type

data Type
    = TPrim TPrim
    | TFun [Type] Type
    | TBox Type
    | TConst TConst
    deriving (Show, Eq, Ord)

data TypedVar = TypedVar
    { tvName :: String
    , tvType :: Type
    }
    deriving (Show, Eq, Ord)

type VariantTypes = [Type]

type Access = Access' Type

type VarBindings = [(TypedVar, Access)]

data DecisionTree
    = DLeaf (VarBindings, Expr)
    | DSwitch Span Access (Map VariantIx DecisionTree) DecisionTree
    | DSwitchStr Access (Map String DecisionTree) DecisionTree
    deriving Show

type Ction = (VariantIx, Span, TConst, [Expr])
type Fun = ([TypedVar], (Expr, Type))

data Expr
    = Lit Const
    | Var Virt TypedVar
    | App Expr [Expr]
    | If Expr Expr Expr
    | Fun Fun
    | Let Def Expr
    | Match [Expr] DecisionTree
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
type Externs = [(String, Type)]

data Program = Program Defs Datas Externs
    deriving Show

instance TypeAst Type where
    tprim = TPrim
    tconst = TConst
    tfun = TFun
    tbox = TBox

    unTconst = \case
        TConst tc -> Just tc
        _ -> Nothing

instance Functor Access' where
    fmap f = \case
        TopSel i t -> TopSel i (f t)
        As a s i ts -> As (fmap f a) s i (map f ts)
        Sel i s a -> Sel i s (fmap f a)
        ADeref a -> ADeref (fmap f a)

instance FreeVars Expr TypedVar where
    freeVars e = fvExpr e

fvExpr :: Expr -> Set TypedVar
fvExpr = \case
    Lit _ -> Set.empty
    Var Virt _ -> Set.empty
    Var NonVirt x -> Set.singleton x
    App f a -> Set.unions (map freeVars (f : a))
    If p c a -> fvIf p c a
    Fun (ps, (b, _)) -> Set.difference (freeVars b) (Set.fromList ps)
    Let (VarDef (lhs, (_, rhs))) e ->
        Set.union (freeVars rhs) (Set.delete lhs (freeVars e))
    Let (RecDefs ds) e -> fvLet (unzip (map (second (Fun . snd)) ds)) e
    Match es dt -> Set.unions (fvDecisionTree dt : map freeVars es)
    Ction (_, _, _, as) -> Set.unions (map freeVars as)
    Sizeof _t -> Set.empty
    Absurd _ -> Set.empty

fvDecisionTree :: DecisionTree -> Set TypedVar
fvDecisionTree = \case
    DLeaf (bs, e) -> Set.difference (freeVars e) (Set.fromList (map fst bs))
    DSwitch _ _ cs def -> fvDSwitch (Map.elems cs) def
    DSwitchStr _ cs def -> fvDSwitch (Map.elems cs) def
    where fvDSwitch es def = Set.unions $ fvDecisionTree def : map fvDecisionTree es
