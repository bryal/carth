{-# LANGUAGE LambdaCase, TypeSynonymInstances, FlexibleInstances
           , MultiParamTypeClasses, KindSignatures, DataKinds
           , DeriveDataTypeable #-}

module Parsed (module Parsed, Const (..), TPrim(..), TConst) where

import qualified Data.Set as Set
import Data.Set (Set)
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
    | TVImplicit String
    deriving (Show, Eq, Ord, Data)

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
    -- TODO: Add special pattern for Lazy
    deriving Show

data Expr'
    = Lit Const
    | Var (Id 'Small)
    | App Expr Expr
    | If Expr Expr Expr
    | Let1 DefLike Expr
    | Let [DefLike] Expr
    | LetRec [Def] Expr
    | TypeAscr Expr Type
    | Match Expr [(Pat, Expr)]
    | FunMatch [(Pat, Expr)]
    | Ctor (Id 'Big)
    | Sizeof Type
    deriving (Show, Eq)

type Expr = WithPos Expr'

data Def = VarDef SrcPos (Id 'Small) (Maybe Scheme) Expr
         | FunDef SrcPos (Id 'Small) (Maybe Scheme) [Pat] Expr
    deriving (Show, Eq)

data DefLike = Def Def | Deconstr Pat Expr
    deriving (Show, Eq)

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
    freeVars = \case
        VarDef _ _ _ body -> freeVars body
        FunDef _ _ _ pats body ->
            Set.difference (freeVars body) (Set.unions (map bvPat pats))

instance FreeVars DefLike (Id 'Small) where
    freeVars = \case
        Def d -> freeVars d
        Deconstr _ matchee -> freeVars matchee

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
fvExpr = unpos >>> fvExpr'
  where
    fvExpr' = \case
        Lit _ -> Set.empty
        Var x -> Set.singleton x
        App f a -> fvApp f a
        If p c a -> fvIf p c a
        Let1 b e -> Set.union (freeVars b) (Set.difference (freeVars e) (bvDefLike b))
        Let bs e -> foldr
            (\b fvs -> Set.union (freeVars b) (Set.difference fvs (bvDefLike b)))
            (freeVars e)
            bs
        LetRec ds e -> fvLet (unzip (map (\d -> (defLhs d, d)) ds)) e
        TypeAscr e _t -> freeVars e
        Match e cs -> fvMatch e cs
        FunMatch cs -> fvCases cs
        Ctor _ -> Set.empty
        Sizeof _t -> Set.empty
    bvDefLike = \case
        Def d -> Set.singleton (defLhs d)
        Deconstr pat _ -> bvPat pat

defLhs :: Def -> Id 'Small
defLhs = \case
    VarDef _ lhs _ _ -> lhs
    FunDef _ lhs _ _ _ -> lhs

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
