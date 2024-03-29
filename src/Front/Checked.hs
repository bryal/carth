module Front.Checked
    ( module Front.Checked
    , TVar(..)
    , TPrim(..)
    , Type
    , TConst
    , TConst'
    , Type'(..)
    , Scheme(..)
    , VariantIx
    , Span
    , Con(..)
    , mainType
    , Virt (..)
    )
where

import Data.Map (Map)
import Data.Word
import Data.Bifunctor
import qualified Data.Map as Map

import Misc
import Front.Inferred
    ( TVar(..)
    , TConst
    , Type
    , Scheme(..)
    , Const(..)
    , VariantIx
    , Span
    , Con(..)
    , Virt(..)
    )
import Front.TypeAst

data TypedVar = TypedVar String Type
    deriving (Show, Eq, Ord)

data Access
    = TopSel Word32 -- type of selectee
    | As Access Span VariantIx
    | Sel Access Word32 Span
    | ADeref Access
    deriving (Show, Eq, Ord)

type VarBindings = Map TypedVar Access

data DecisionTree
    = DLeaf (VarBindings, Expr)
    | DSwitch Span Access (Map VariantIx DecisionTree) DecisionTree
    | DSwitchStr Access (Map String DecisionTree) DecisionTree
    deriving Show

type Fun = ([(String, Type)], (Expr, Type))

type Var = (Virt, TypedVar)

data Expr
    = Lit Const
    | Var Var
    | App Expr [Expr]
    | If Expr Expr Expr
    | Fun Fun
    | Let Def Expr
    | Match [Expr] DecisionTree
    | Ction VariantIx Span TConst [Expr]
    | Sizeof Type
    | Absurd Type
    deriving (Show)

builtinExterns :: Map String Type
builtinExterns = Map.fromList
    [ ("GC_add_roots", TFun [TBox tUnit, TBox tUnit] tUnit)
    , ("GC_malloc", TFun [TPrim TNatSize] (TBox tUnit))
    , ("malloc", TFun [TPrim TNatSize] (TBox tUnit))
    , ("str_eq", TFun [tStr, tStr] tBool)
    , ("carth_backtrace_push", TFun [tStr] tUnit)
    , ("carth_backtrace_pop", TFun [] tUnit)
    ]

type Defs = TopologicalOrder Def
data Def = VarDef VarDef | RecDefs RecDefs deriving Show
type VarDef = (String, (Scheme, Expr))
type RecDefs = [(String, (Scheme, Fun))]
type TypeDefs = Map String ([TVar], [(String, [Type])])
type Externs = Map String Type

data Program = Program Defs TypeDefs Externs
    deriving Show


flattenDefs :: Defs -> [(String, (Scheme, Expr))]
flattenDefs (Topo defs) = defToVarDefs =<< defs

defToVarDefs :: Def -> [(String, (Scheme, Expr))]
defToVarDefs = \case
    VarDef d -> [d]
    RecDefs ds -> map funDefToVarDef ds

funDefToVarDef :: (String, (Scheme, Fun)) -> VarDef
funDefToVarDef = second (second Fun)
