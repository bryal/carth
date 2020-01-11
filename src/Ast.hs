{-# LANGUAGE LambdaCase, TypeSynonymInstances, FlexibleInstances
           , MultiParamTypeClasses, TemplateHaskell, KindSignatures
           , DataKinds #-}

module Ast
    ( TVar(..)
    , TPrim(..)
    , TConst
    , Type(..)
    , Scheme(..)
    , scmParams
    , scmBody
    , IdCase(..)
    , Id(..)
    , idstr
    , Const(..)
    , Pat(..)
    , Expr'(..)
    , Expr
    , Def
    , ConstructorDefs(..)
    , TypeDef(..)
    , Extern(..)
    , Program(..)
    , startType
    , isFunLike
    )
where

import qualified Data.Set as Set
import Data.Set (Set)
import Control.Lens (makeLenses)
import Control.Arrow ((>>>))

import SrcPos
import FreeVars


data IdCase = Big | Small

newtype Id (case' :: IdCase) = Id (WithPos String)
    deriving (Show, Eq, Ord)

data TVar
    = TVExplicit (Id 'Small)
    | TVImplicit Int
    deriving (Show, Eq, Ord)

data TPrim
    = TUnit
    | TNat8
    | TNat16
    | TNat32
    | TNat
    | TInt8
    | TInt16
    | TInt32
    | TInt
    | TDouble
    | TBool
    deriving (Show, Eq, Ord)

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

data Pat
    = PConstruction SrcPos (Id 'Big) [Pat]
    | PInt SrcPos Int
    | PBool SrcPos Bool
    | PStr SrcPos String
    | PVar (Id 'Small)
    | PBox SrcPos Pat
    deriving Show

data Const
    = Unit
    | Int Int
    | Double Double
    | Str String
    | Bool Bool
    deriving (Show, Eq)

data Expr'
    = Lit Const
    | Var (Id 'Small)
    | App Expr Expr
    | If Expr Expr Expr
    | Fun Pat Expr
    | Let [Def] Expr
    | TypeAscr Expr Type
    | Match Expr [(Pat, Expr)]
    | FunMatch [(Pat, Expr)]
    | Ctor (Id 'Big)
    | Box Expr
    | Deref Expr
    deriving (Show, Eq)

type Expr = WithPos Expr'

type Def = (Id 'Small, (Maybe (WithPos Scheme), Expr))

newtype ConstructorDefs = ConstructorDefs [(Id 'Big, [Type])]
    deriving (Show, Eq)

data TypeDef = TypeDef (Id 'Big) [Id 'Small] ConstructorDefs
    deriving (Show, Eq)

data Extern = Extern (Id 'Small) Type
    deriving (Show, Eq)

data Program = Program [Def] [TypeDef] [Extern]
    deriving (Show, Eq)


instance Eq Pat where
    (==) = curry $ \case
        (PConstruction _ x ps, PConstruction _ x' ps') -> x == x' && ps == ps'
        (PVar x, PVar x') -> x == x'
        _ -> False

instance FreeVars Def (Id 'Small) where
    freeVars (_, (_, body)) = freeVars body

instance FreeVars Expr (Id 'Small) where
    freeVars = fvExpr

instance HasPos (Id a) where
    getPos (Id x) = getPos x

instance HasPos Pat where
    getPos = \case
        PConstruction p _ _ -> p
        PInt p _ -> p
        PBool p _ -> p
        PStr p _ -> p
        PVar v -> getPos v
        PBox p _ -> p


fvExpr :: Expr -> Set (Id 'Small)
fvExpr = unpos >>> \case
    Lit _ -> Set.empty
    Var x -> Set.singleton x
    App f a -> fvApp f a
    If p c a -> fvIf p c a
    Fun p b -> fvFun' p b
    Let bs e -> fvLet (Set.fromList (map fst bs), map (snd . snd) bs) e
    TypeAscr e _ -> freeVars e
    Match e cs -> fvMatch e cs
    FunMatch cs -> fvCases cs
    Ctor _ -> Set.empty
    Box e -> fvExpr e
    Deref e -> fvExpr e

fvFun' :: Pat -> Expr -> Set (Id 'Small)
fvFun' p e = Set.difference (freeVars e) (bvPat p)

fvMatch :: Expr -> [(Pat, Expr)] -> Set (Id 'Small)
fvMatch e cs = Set.union (freeVars e) (fvCases cs)

fvCases :: [(Pat, Expr)] -> Set (Id 'Small)
fvCases = Set.unions . map (\(p, e) -> Set.difference (freeVars e) (bvPat p))

bvPat :: Pat -> Set (Id 'Small)
bvPat = \case
    PConstruction _ _ ps -> Set.unions (map bvPat ps)
    PInt _ _ -> Set.empty
    PBool _ _ -> Set.empty
    PStr _ _ -> Set.empty
    PVar x -> Set.singleton x
    PBox _ p -> bvPat p

idstr :: Id a -> String
idstr (Id (WithPos _ x)) = x

startType :: Type
startType = TFun (TPrim TUnit) (TPrim TUnit)

isFunLike :: Expr -> Bool
isFunLike (WithPos _ e) = case e of
    Fun _ _ -> True
    FunMatch _ -> True
    _ -> False
