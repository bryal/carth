{-# LANGUAGE LambdaCase, TypeSynonymInstances, FlexibleInstances
           , MultiParamTypeClasses, TemplateHaskell #-}

module Ast
    ( TVar(..)
    , TPrim(..)
    , Type(..)
    , Scheme(..)
    , scmParams
    , scmBody
    , Id(..)
    , Const(..)
    , Pat(..)
    , Expr(..)
    , Def
    , TypeDefConstructor(..)
    , TypeDef(..)
    , Program(..)
    , mainType
    )
where

import Data.String
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List
import Control.Lens (makeLenses)

import Misc
import FreeVars
import NonEmpty

newtype Id =
    Id String
    deriving (Show, Eq, Ord)

data TVar
    = TVExplicit Id
    | TVImplicit Int
    deriving (Show, Eq, Ord)

data TPrim
    = TUnit
    | TInt
    | TDouble
    | TChar
    | TStr
    | TBool
    deriving (Show, Eq, Ord)

data Type
    = TVar TVar
    | TPrim TPrim
    | TConst String [Type]
    | TFun Type
           Type
    deriving (Show, Eq, Ord)

data Scheme = Forall
    { _scmParams :: (Set TVar)
    , _scmBody :: Type
    } deriving (Show, Eq)
makeLenses ''Scheme

data Pat
    = PConstructor String
    | PConstruction String
                    (NonEmpty Pat)
    | PVar Id
    deriving (Show, Eq)

data Const
    = Unit
    | Int Int
    | Double Double
    | Char Char
    | Str String
    | Bool Bool
    deriving (Show, Eq)

data Expr
    = Lit Const
    | Var Id
    | App Expr
          Expr
    | If Expr
         Expr
         Expr
    | Fun Id
          Expr
    | Let (NonEmpty Def)
          Expr
    | TypeAscr Expr Type
    | Match Expr
            (NonEmpty (Pat, Expr))
    | FunMatch (NonEmpty (Pat, Expr))
    | Constructor String
    deriving (Show, Eq)

type Def = (Id, (Maybe Scheme, Expr))

data TypeDefConstructor = TypeDefConstructor String [Type]
    deriving (Show, Eq)

data TypeDef = TypeDef String [Id] [TypeDefConstructor]
     deriving (Show, Eq)

data Program = Program (Maybe Scheme, Expr) [Def] [TypeDef]
    deriving (Show, Eq)

mainType :: Type
mainType = TFun (TPrim TUnit) (TPrim TUnit)

instance IsString Id where
    fromString = Id

instance FreeVars Def Id where
    freeVars (name, (_, body)) = Set.delete name (freeVars body)

instance FreeVars Expr Id where
    freeVars = fvExpr

fvExpr :: Expr -> Set Id
fvExpr = \case
    Lit c -> fvLit c
    Var x -> fvVar x
    App f a -> fvApp f a
    If p c a -> fvIf p c a
    Fun p b -> fvFun p b
    Let bs e ->
        fvLet (Set.fromList (fromList1 (map1 fst bs)), map1 (snd . snd) bs) e
    TypeAscr e _ -> freeVars e
    Match e cs -> fvMatch e (fromList1 cs)
    FunMatch _ -> nyi "fvExpr FunMatch"
    Constructor _ -> nyi "fvExpr Constructor"

instance Pattern Pat Id where
    patternBoundVars = bvPat

bvPat :: Pat -> Set Id
bvPat = \case
    PConstructor _ -> Set.empty
    PConstruction _ ps -> Set.unions (map1 bvPat ps)
    PVar x -> Set.singleton x

instance Pretty Scheme             where pretty' _ = prettyScheme
instance Pretty Type               where pretty' _ = prettyType
instance Pretty TPrim              where pretty' _ = prettyTPrim
instance Pretty TVar               where pretty' _ = prettyTVar

prettyScheme :: Scheme -> String
prettyScheme (Forall ps t) = concat
    [ "(forall ["
    , intercalate " " (map pretty (Set.toList ps))
    , "] "
    , pretty t
    , ")"
    ]

prettyType :: Type -> String
prettyType = \case
    Ast.TVar tv -> pretty tv
    Ast.TPrim c -> pretty c
    Ast.TFun a b -> concat ["(Fun ", pretty a, " ", pretty b, ")"]
    Ast.TConst c ts -> case ts of
        [] -> c
        ts -> concat ["(", c, precalate " " (map pretty ts), ")"]

prettyTPrim :: TPrim -> String
prettyTPrim = \case
    TUnit -> "Unit"
    TInt -> "Int"
    TDouble -> "Double"
    TChar -> "Char"
    TStr -> "Str"
    TBool -> "Bool"

prettyTVar :: TVar -> String
prettyTVar = \case
    TVExplicit (Id v) -> v
    TVImplicit n -> "#" ++ show n
