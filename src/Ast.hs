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
import Data.List
import Data.Bifunctor
import Control.Lens (makeLenses)
import Control.Arrow ((>>>))

import Misc
import SrcPos
import FreeVars
import NonEmpty

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
    | TChar
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
    | PVar (Id 'Small)
    | PBox SrcPos Pat
    deriving Show

data Const
    = Unit
    | Int Int
    | Double Double
    | Char Char
    | Str String
    | Bool Bool
    deriving (Show, Eq)

data Expr'
    = Lit Const
    | Var (Id 'Small)
    | App Expr Expr
    | If Expr Expr Expr
    | Fun Pat Expr
    | Let (NonEmpty Def) Expr
    | TypeAscr Expr Type
    | Match Expr (NonEmpty (Pat, Expr))
    | FunMatch (NonEmpty (Pat, Expr))
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
        PVar v -> getPos v
        PBox p _ -> p

instance Pretty Program where
    pretty' = prettyProg
instance Pretty Extern where
    pretty' = prettyExtern
instance Pretty ConstructorDefs where
    pretty' = prettyConstructorDefs
instance Pretty TypeDef where
    pretty' = prettyTypeDef
instance Pretty Expr' where
    pretty' = prettyExpr'
instance Pretty Pat where
    pretty' _ = prettyPat
instance Pretty Const where
    pretty' _ = prettyConst
instance Pretty Scheme where
    pretty' _ = prettyScheme
instance Pretty Type where
    pretty' _ = prettyType
instance Pretty TPrim where
    pretty' _ = prettyTPrim
instance Pretty TVar where
    pretty' _ = prettyTVar
instance Pretty (Id a) where
    pretty' _ = idstr


fvExpr :: Expr -> Set (Id 'Small)
fvExpr = unpos >>> \case
    Lit _ -> Set.empty
    Var x -> Set.singleton x
    App f a -> fvApp f a
    If p c a -> fvIf p c a
    Fun p b -> fvFun' p b
    Let bs e ->
        fvLet (Set.fromList (fromList1 (map1 fst bs)), map1 (snd . snd) bs) e
    TypeAscr e _ -> freeVars e
    Match e cs -> fvMatch e (fromList1 cs)
    FunMatch cs -> fvCases (fromList1 cs)
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
    PVar x -> Set.singleton x
    PBox _ p -> bvPat p

prettyProg :: Int -> Program -> String
prettyProg d (Program defs tdefs externs) =
    let
        prettyDef = \case
            (name, (Just scm, body)) -> concat
                [ indent d ++ "(define: " ++ pretty name ++ "\n"
                , indent (d + 4) ++ pretty' (d + 4) scm ++ "\n"
                , indent (d + 2) ++ pretty' (d + 2) body ++ ")"
                ]
            (name, (Nothing, body)) -> concat
                [ indent d ++ "(define " ++ pretty name ++ "\n"
                , indent (d + 2) ++ pretty' (d + 2) body ++ ")"
                ]
    in unlines (map prettyDef defs ++ map pretty tdefs ++ map pretty externs)

prettyExtern :: Int -> Extern -> String
prettyExtern _ (Extern name t) =
    concat ["(extern ", idstr name, " ", pretty t, ")"]

prettyTypeDef :: Int -> TypeDef -> String
prettyTypeDef d (TypeDef name params constrs) = concat
    [ "(type "
    , if null params
        then pretty name
        else "(" ++ pretty name ++ " " ++ spcPretty params ++ ")"
    , "\n" ++ indent (d + 2) ++ pretty' (d + 2) constrs ++ ")"
    ]

prettyConstructorDefs :: Int -> ConstructorDefs -> String
prettyConstructorDefs d (ConstructorDefs cs) = intercalate
    ("\n" ++ indent d)
    (map prettyConstrDef cs)
  where
    prettyConstrDef = \case
        (c, []) -> pretty c
        (c, ts) -> concat ["(", pretty c, " ", spcPretty ts, ")"]

prettyExpr' :: Int -> Expr' -> String
prettyExpr' d = \case
    Lit l -> pretty l
    Var v -> idstr v
    App f x -> concat
        [ "(" ++ pretty' (d + 1) f ++ "\n"
        , indent (d + 1) ++ pretty' (d + 1) x ++ ")"
        ]
    If pred' cons alt -> concat
        [ "(if " ++ pretty' (d + 4) pred' ++ "\n"
        , indent (d + 4) ++ pretty' (d + 4) cons ++ "\n"
        , indent (d + 2) ++ pretty' (d + 2) alt ++ ")"
        ]
    Fun param body -> concat
        [ "(fun ("
        , prettyPat param
        , ")\n"
        , indent (d + 2)
        , pretty' (d + 2) body
        , ")"
        ]
    Let binds body -> concat
        [ "(let ["
        , intercalate1 ("\n" ++ indent (d + 6)) (map1 (prettyDef (d + 6)) binds)
        , "]\n"
        , indent (d + 2) ++ pretty' (d + 2) body ++ ")"
        ]
      where
        prettyDef d' = \case
            (name, (Just scm, dbody)) -> concat
                [ "[: " ++ pretty' (d' + 3) name ++ "\n"
                , indent (d' + 3) ++ pretty' (d' + 3) scm ++ "\n"
                , indent (d' + 1) ++ pretty' (d' + 1) dbody ++ "]"
                ]
            (name, (Nothing, dbody)) -> concat
                [ "[" ++ pretty' (d' + 1) name ++ "\n"
                , indent (d' + 1) ++ pretty' (d' + 1) dbody ++ "]"
                ]
    TypeAscr e t ->
        concat ["(: ", pretty' (d + 3) e, "\n", pretty' (d + 3) t, ")"]
    Match e cs -> concat
        [ "(match " ++ pretty' (d + 7) e
        , precalate1
            ("\n" ++ indent (d + 2))
            (map1 (prettyBracketPair (d + 2)) cs)
        , ")"
        ]
    FunMatch cs -> concat
        [ "(fun-match"
        , precalate1
            ("\n" ++ indent (d + 2))
            (map1 (prettyBracketPair (d + 2)) cs)
        , ")"
        ]
    Ctor c -> pretty c
    Box e -> concat ["(box ", pretty' (d + 5) e, ")"]
    Deref e -> concat ["(deref ", pretty' (d + 7) e, ")"]

prettyPat :: Pat -> String
prettyPat = \case
    PConstruction _ (Id (WithPos _ c)) ps ->
        if null ps then c else concat ["(", c, " ", spcPretty ps, ")"]
    PInt _ n -> show n
    PBool _ b -> if b then "true" else "false"
    PVar v -> idstr v
    PBox _ p -> "(Box " ++ prettyPat p ++ ")"

prettyConst :: Const -> String
prettyConst = \case
    Unit -> "unit"
    Int n -> show n
    Double x -> show x
    Char c -> showChar' c
    Str s -> '"' : (s >>= showChar'') ++ "\""
    Bool b -> if b then "true" else "false"

prettyScheme :: Scheme -> String
prettyScheme (Forall ps t) =
    concat ["(forall [" ++ spcPretty (Set.toList ps) ++ "] ", pretty t ++ ")"]

prettyType :: Type -> String
prettyType = \case
    Ast.TVar tv -> pretty tv
    Ast.TPrim c -> pretty c
    Ast.TFun a b -> prettyTFun a b
    Ast.TBox t -> "(Box " ++ pretty t ++ ")"
    Ast.TConst (c, ts) -> case ts of
        [] -> c
        _ -> concat ["(", c, " ", spcPretty ts, ")"]

prettyTFun :: Type -> Type -> String
prettyTFun a b =
    let
        (bParams, bBody) = f b
        f = \case
            TFun a' b' -> first (a' :) (f b')
            t -> ([], t)
    in concat ["(Fun ", pretty a, " ", spcPretty (bParams ++ [bBody]), ")"]

prettyTPrim :: TPrim -> String
prettyTPrim = \case
    TUnit -> "Unit"
    TNat8 -> "Nat8"
    TNat16 -> "Nat16"
    TNat32 -> "Nat32"
    TNat -> "Nat"
    TInt8 -> "Int8"
    TInt16 -> "Int16"
    TInt32 -> "Int32"
    TInt -> "Int"
    TDouble -> "Double"
    TChar -> "Char"
    TBool -> "Bool"

prettyTVar :: TVar -> String
prettyTVar = \case
    TVExplicit v -> idstr v
    TVImplicit n -> "#" ++ show n

spcPretty :: Pretty a => [a] -> String
spcPretty = unwords . map pretty

idstr :: Id a -> String
idstr (Id (WithPos _ x)) = x

startType :: Type
startType = TFun (TPrim TUnit) (TPrim TUnit)

isFunLike :: Expr -> Bool
isFunLike (WithPos _ e) = case e of
    Fun _ _ -> True
    FunMatch _ -> True
    _ -> False
