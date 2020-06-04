{-# LANGUAGE LambdaCase #-}

module Checked
    ( module Checked
    , TVar(..)
    , TPrim(..)
    , TConst
    , Type(..)
    , Scheme(..)
    , VariantIx
    , Span
    , Con(..)
    , mainType
    )
where

import Data.Map.Strict (Map)
import Data.Word
import Data.Bifunctor

import Misc
import SrcPos
import Inferred
    ( TVar(..)
    , TPrim(..)
    , TConst
    , Type(..)
    , Scheme(..)
    , Const(..)
    , VariantIx
    , Span
    , Con(..)
    , mainType
    )
import qualified Inferred

data TypedVar = TypedVar String Type
    deriving (Show, Eq, Ord)

data Access
    = Obj
    | As Access Span [Type]
    | Sel Word32 Span Access
    | ADeref Access
    deriving (Show, Eq, Ord)

type VarBindings = Map TypedVar Access

data DecisionTree
    = DLeaf (VarBindings, Expr)
    | DSwitch Access (Map VariantIx DecisionTree) DecisionTree
    | DSwitchStr Access (Map String DecisionTree) DecisionTree
    deriving Show

type Fun = ((String, Type), (Expr, Type))

data Expr'
    = Lit Const
    | Var TypedVar
    | App Expr Expr Type
    | If Expr Expr Expr
    | Fun Fun
    | Let Def Expr
    | Match Expr DecisionTree Type
    | Ction VariantIx Span TConst [Expr]
    | Sizeof Type
    | Absurd Type
    deriving (Show)

data Expr = Expr (Maybe SrcPos) Expr'
    deriving (Show)


builtinExterns :: Map String Type
builtinExterns = fmap fst Inferred.builtinExterns

withPos :: SrcPos -> Expr' -> Expr
withPos = Expr . Just

noPos :: Expr' -> Expr
noPos = Checked.Expr Nothing

type Defs = TopologicalOrder Def
data Def = VarDef VarDef | RecDefs RecDefs deriving Show
type VarDef = (String, WithPos (Scheme, Expr))
type RecDefs = [(String, WithPos (Scheme, WithPos Fun))]
type TypeDefs = Map String ([TVar], [[Type]])
type Externs = Map String (Type, SrcPos)

data Program = Program Defs TypeDefs Externs
    deriving (Show)


flattenDefs :: Defs -> [(String, WithPos (Scheme, Expr))]
flattenDefs (Topo defs) = defToVarDefs =<< defs

defToVarDefs :: Def -> [(String, WithPos (Scheme, Expr))]
defToVarDefs = \case
    VarDef d -> [d]
    RecDefs ds -> map funDefToVarDef ds

funDefToVarDef :: (String, WithPos (Scheme, WithPos Fun)) -> VarDef
funDefToVarDef = second (mapPosd (second (\(WithPos p f) -> Expr (Just p) (Fun f))))
