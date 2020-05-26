{-# LANGUAGE LambdaCase, TypeSynonymInstances, FlexibleInstances
           , MultiParamTypeClasses, KindSignatures, DataKinds #-}

module Parsed where

import qualified Data.Set as Set
import Data.Set (Set)
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
    = TNat8
    | TNat16
    | TNat32
    | TNat
    | TInt8
    | TInt16
    | TInt32
    | TInt
    | TF64
    deriving (Show, Eq, Ord)

type TConst = (String, [Type])

-- TODO: Now that AnnotAst.Type is not just an alias to Ast.Type, it makes sense
--       to add SrcPos-itions to Ast.Type! Would simplify / improve error
--       messages quite a bit.
data Type
    = TVar TVar
    | TPrim TPrim
    | TConst TConst
    | TFun Type Type
    | TBox Type
    deriving (Show, Eq, Ord)

data Scheme = Forall SrcPos (Set TVar) Type
     deriving (Show, Eq)

data Pat
    = PConstruction SrcPos (Id 'Big) [Pat]
    | PInt SrcPos Int
    | PStr SrcPos String
    | PVar (Id 'Small)
    | PBox SrcPos Pat
    deriving Show

data Const
    = Int Int
    | F64 Double
    | Str String
    deriving (Show, Eq)

data Expr'
    = Lit Const
    | Var (Id 'Small)
    | App Expr Expr
    | If Expr Expr Expr
    | Let [Def] Expr
    | TypeAscr Expr Type
    | Match Expr [(Pat, Expr)]
    | FunMatch [(Pat, Expr)]
    | Ctor (Id 'Big)
    | Box Expr
    | Deref Expr
    | Transmute Expr
    deriving (Show, Eq)

type Expr = WithPos Expr'

type Def = (Id 'Small, (WithPos (Maybe Scheme, Expr)))

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
    Let bs e -> fvLet (Set.fromList (map fst bs), map (snd . unpos . snd) bs) e
    TypeAscr e _ -> freeVars e
    Match e cs -> fvMatch e cs
    FunMatch cs -> fvCases cs
    Ctor _ -> Set.empty
    Box e -> fvExpr e
    Deref e -> fvExpr e
    Transmute e -> fvExpr e

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

mainType :: Type
mainType = TFun (TConst tUnit) (TConst tUnit)

tUnit :: (String, [a])
tUnit = ("Unit", [])

isFunLike :: Expr -> Bool
isFunLike (WithPos _ e) = case e of
    FunMatch _ -> True
    _ -> False
