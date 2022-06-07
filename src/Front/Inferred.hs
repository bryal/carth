{-# LANGUAGE TemplateHaskell, DataKinds #-}

-- TODO: Can this and Checked be merged to a single, parametrized AST?

-- | Type annotated AST as a result of typechecking
module Front.Inferred (module Front.Inferred, Type, TConst, WithPos(..), TVar(..), TPrim(..), Const(..), Type' (..), TConst') where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import Data.Bifunctor
import Lens.Micro.Platform (makeLenses)

import Misc
import qualified Front.Parsed as Parsed
import Front.Parsed (Type, TConst, TVar(..), Const(..))
import Front.SrcPos
import Front.TypeAst


data TypeErr
    = MainNotDefined
    | InvalidUserTypeSig SrcPos Scheme Scheme
    | CtorArityMismatch SrcPos String Int Int
    | ConflictingPatVarDefs SrcPos String
    | UndefCtor SrcPos String
    | UndefVar SrcPos String
    | InfType SrcPos Type Type TVar Type
    | UnificationFailed SrcPos Type Type Type Type
    | ConflictingTypeDef SrcPos String
    | ConflictingCtorDef SrcPos String
    | RedundantCase SrcPos
    | InexhaustivePats SrcPos String
    | ExternNotMonomorphic (Parsed.Id 'Parsed.Small) TVar
    | FoundHole SrcPos
    | RecTypeDef String SrcPos
    | UndefType SrcPos String
    | WrongMainType SrcPos Parsed.Scheme
    | RecursiveVarDef (WithPos String)
    | TypeInstArityMismatch SrcPos String Int Int
    | ConflictingVarDef SrcPos String
    | NoClassInstance SrcPos ClassConstraint
    | FunCaseArityMismatch SrcPos Int Int
    | FunArityMismatch SrcPos Int Int
    deriving (Show)

type ClassConstraint = (String, [Type])

data Scheme = Forall
    { _scmParams :: Set TVar
    , _scmConstraints :: Set ClassConstraint
    , _scmBody :: Type
    }
    deriving (Show, Eq)
makeLenses ''Scheme

type Id = WithPos String

data TypedVar = TypedVar Id Type
    deriving (Show, Eq, Ord)

type VariantIx = Integer

type Span = Integer

data Variant = VariantIx VariantIx | VariantStr String
    deriving (Show, Eq, Ord)

data Con = Con
    { variant :: Variant
    , span :: Span
    , argTs :: [Type]
    }
    deriving Show

data Pat'
    = PVar TypedVar
    | PWild
    | PCon Con [Pat]
    | PBox Pat
    deriving Show

data Pat = Pat SrcPos Type Pat'
    deriving Show

type Cases = [(WithPos [Pat], Expr)]
type FunMatch = (Cases, [Type], Type)

-- | Whether a Var refers to a builtin virtual, or a global/local definition. So we don't
--   have to keep as much state about environment definitions in later passes.
data Virt = Virt | NonVirt deriving (Show, Eq)

type Var = (Virt, TypedVar)

data Expr'
    = Lit Const
    | Var Var
    | App Expr [Expr] Type
    | If Expr Expr Expr
    | Let Def Expr
    | FunMatch FunMatch
    | Ctor VariantIx Span TConst [Type]
    | Sizeof Type
    deriving Show

type Expr = WithPos Expr'

type Defs = TopologicalOrder Def
data Def = VarDef VarDef | RecDefs RecDefs deriving Show
type VarDef = (String, (Scheme, Expr))
type RecDefs = [(String, (Scheme, WithPos FunMatch))]
type TypeDefs = Map String ([TVar], [(Id, [Type])])
type Ctors = Map String (VariantIx, (String, [TVar]), [Type], Span)
type Externs = Map String Type


instance Eq Con where
    (==) (Con c1 _ _) (Con c2 _ _) = c1 == c2

instance Ord Con where
    compare (Con c1 _ _) (Con c2 _ _) = compare c1 c2


ftv :: Type -> Set TVar
ftv = \case
    TVar tv -> Set.singleton tv
    TPrim _ -> Set.empty
    TFun pts rt -> Set.unions (ftv rt : map ftv pts)
    TBox t -> ftv t
    TConst (_, ts) -> Set.unions (map ftv ts)

defSigs :: Def -> [(String, Scheme)]
defSigs = \case
    VarDef d -> [defSig d]
    RecDefs ds -> map defSig ds

defSig :: (String, (Scheme, a)) -> (String, Scheme)
defSig = second fst

flattenDefs :: Defs -> [(String, (Scheme, Expr))]
flattenDefs (Topo defs) = defToVarDefs =<< defs

defToVarDefs :: Def -> [(String, (Scheme, Expr))]
defToVarDefs = \case
    VarDef d -> [d]
    RecDefs ds -> map (second (second (mapPosd FunMatch))) ds
