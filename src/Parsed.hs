{-# LANGUAGE LambdaCase, TypeSynonymInstances, FlexibleInstances
           , MultiParamTypeClasses, KindSignatures, DataKinds
           , DeriveDataTypeable #-}

module Parsed (module Parsed, Const (..), TPrim(..), TConst) where

import qualified Data.Set as Set
import Data.Set (Set)
import Data.Bifunctor
import Control.Arrow ((>>>))
import Data.Data

import SrcPos
import FreeVars
import TypeAst
import Lexd (Const (..))


data IdCase = Big | Small

newtype Id (case' :: IdCase) = Id (WithPos String)
    deriving (Show, Eq, Ord, Data)

data TVar
    = TVExplicit (Id 'Small)
    | TVImplicit Word
    deriving (Show, Eq, Ord, Data)

-- TODO: Now that AnnotAst.Type is not just an alias to Ast.Type, it makes sense
--       to add SrcPos-itions to Ast.Type! Would simplify / improve error
--       messages quite a bit.
data Type
    = TVar TVar
    | TPrim TPrim
    | TConst (TConst Type)
    -- TODO: Remove special case for these two? Is it really needed?
    | TFun Type Type
    | TBox Type
    deriving (Show, Eq, Ord, Data)

data Scheme = Forall SrcPos (Set TVar) Type
     deriving (Show, Eq, Data)

data Pat
    = PConstruction SrcPos (Id 'Big) [Pat]
    | PInt SrcPos Int
    | PStr SrcPos String
    | PVar (Id 'Small)
    | PBox SrcPos Pat
    deriving Show

data Expr'
    = Lit Const
    | Var (Id 'Small)
    | App Expr Expr
    | If Expr Expr Expr
    | Let1 Def Expr
    | LetRec [Def] Expr
    | TypeAscr Expr Type
    | Match Expr [(Pat, Expr)]
    | FunMatch [(Pat, Expr)]
    | Ctor (Id 'Big)
    | Sizeof Type
    deriving (Show, Eq)

type Expr = WithPos Expr'

type Def = (Id 'Small, WithPos (Maybe Scheme, Expr))

newtype ConstructorDefs = ConstructorDefs [(Id 'Big, [Type])]
    deriving (Show, Eq)

data TypeDef = TypeDef (Id 'Big) [Id 'Small] ConstructorDefs
    deriving (Show, Eq)

data Extern = Extern (Id 'Small) Type
    deriving (Show, Eq)

data Program = Program [Def] [TypeDef] [Extern]
    deriving (Show, Eq)


instance TypeAst Type where
    tprim = TPrim
    tconst = TConst
    tfun = TFun
    tbox = TBox

instance Eq Pat where
    (==) = curry $ \case
        (PConstruction _ x ps, PConstruction _ x' ps') -> x == x' && ps == ps'
        (PVar x, PVar x') -> x == x'
        _ -> False

instance FreeVars Def (Id 'Small) where
    freeVars (_, (WithPos _ (_, body))) = freeVars body

instance FreeVars Expr (Id 'Small) where
    freeVars = fvExpr

instance HasPos (Id a) where
    getPos (Id x) = getPos x

instance HasPos Pat where
    getPos = \case
        PConstruction p _ _ -> p
        PInt p _ -> p
        PStr p _ -> p
        PVar v -> getPos v
        PBox p _ -> p


fvExpr :: Expr -> Set (Id 'Small)
fvExpr = unpos >>> \case
    Lit _ -> Set.empty
    Var x -> Set.singleton x
    App f a -> fvApp f a
    If p c a -> fvIf p c a
    Let1 (lhs, WithPos _ (_, rhs)) e ->
        Set.union (freeVars rhs) (Set.delete lhs (freeVars e))
    LetRec ds e -> fvLet (unzip (map (second (snd . unpos)) ds)) e
    TypeAscr e _t -> freeVars e
    Match e cs -> fvMatch e cs
    FunMatch cs -> fvCases cs
    Ctor _ -> Set.empty
    Sizeof _t -> Set.empty

fvMatch :: Expr -> [(Pat, Expr)] -> Set (Id 'Small)
fvMatch e cs = Set.union (freeVars e) (fvCases cs)

fvCases :: [(Pat, Expr)] -> Set (Id 'Small)
fvCases = Set.unions . map (\(p, e) -> Set.difference (freeVars e) (bvPat p))

bvPat :: Pat -> Set (Id 'Small)
bvPat = \case
    PConstruction _ _ ps -> Set.unions (map bvPat ps)
    PInt _ _ -> Set.empty
    PStr _ _ -> Set.empty
    PVar x -> Set.singleton x
    PBox _ p -> bvPat p

idstr :: Id a -> String
idstr (Id (WithPos _ x)) = x
