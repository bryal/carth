{-# LANGUAGE LambdaCase, TemplateHaskell, DataKinds, TupleSections #-}

-- | Type annotated AST as a result of typechecking
module Inferred
    ( module Inferred
    , WithPos(..)
    , TVar(..)
    , TPrim(..)
    , Const(..)
    )
where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Bifunctor
import Lens.Micro.Platform (makeLenses)

import Misc
import qualified Parsed
import Parsed (TVar(..), TPrim(..), Const(..), tUnit)
import SrcPos


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
    | UnboundTVar SrcPos
    | WrongMainType SrcPos Parsed.Scheme
    | RecursiveVarDef (WithPos String)
    | TypeInstArityMismatch SrcPos String Int Int
    | ConflictingVarDef SrcPos String
    deriving Show

type TConst = (String, [Type])

data Type
    = TVar TVar
    | TPrim TPrim
    | TConst TConst
    | TFun Type Type
    | TBox Type
    deriving (Show, Eq, Ord)

data Scheme = Forall
    { _scmParams :: (Set TVar)
    , _scmBody :: Type
    } deriving (Show, Eq)
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
type Pat = WithPos Pat'

type Cases = [(Pat, Expr)]
type FunMatch = (Cases, Type, Type)

data Expr'
    = Lit Const
    | Var TypedVar
    | App Expr Expr Type
    | If Expr Expr Expr
    | Let Def Expr
    | FunMatch FunMatch
    | Ctor VariantIx Span TConst [Type]
    | Sizeof Type
    | Deref Expr
    | Store Expr Expr
    | Transmute Expr Type Type
    deriving Show

type Expr = WithPos Expr'

type Defs = TopologicalOrder Def
data Def = VarDef VarDef | RecDefs RecDefs deriving Show
type VarDef = (String, WithPos (Scheme, Expr))
type RecDefs = [(String, WithPos (Scheme, WithPos FunMatch))]
type TypeDefs = Map String ([TVar], [(Id, [Type])])
type Ctors = Map String (VariantIx, (String, [TVar]), [Type], Span)
type Externs = Map String (Type, SrcPos)


instance Eq Con where
    (==) (Con c1 _ _) (Con c2 _ _) = c1 == c2

instance Ord Con where
    compare (Con c1 _ _) (Con c2 _ _) = compare c1 c2


ftv :: Type -> Set TVar
ftv = \case
    TVar tv -> Set.singleton tv
    TPrim _ -> Set.empty
    TFun t1 t2 -> Set.union (ftv t1) (ftv t2)
    TBox t -> ftv t
    TConst (_, ts) -> Set.unions (map ftv ts)

builtinExterns :: Map String (Inferred.Type, SrcPos)
builtinExterns = Map.fromList $ map
    (second (, SrcPos "<builtin>" 0 0))
    [("GC_malloc", TFun (TPrim TInt) (TBox (TConst tUnit)))]

defSigs :: Def -> [(String, Scheme)]
defSigs = \case
    VarDef d -> [defSig d]
    RecDefs ds -> map defSig ds
    where defSig d = (fst d, fst (unpos (snd d)))

flattenDefs :: Defs -> [(String, WithPos (Scheme, Expr))]
flattenDefs (Topo defs) = defToVarDefs =<< defs

defToVarDefs :: Def -> [(String, WithPos (Scheme, Expr))]
defToVarDefs = \case
    VarDef d -> [d]
    RecDefs ds -> map (second (mapPosd (second (mapPosd FunMatch)))) ds

mainType :: Type
mainType = TFun (TConst tUnit) (TConst tUnit)

tBool :: Type
tBool = TConst ("Bool", [])
