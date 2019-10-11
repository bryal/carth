{-# LANGUAGE LambdaCase, TypeSynonymInstances, FlexibleInstances
           , MultiParamTypeClasses, TemplateHaskell #-}

module Ast
    ( TVar(..)
    , TPrim(..)
    , Type(..)
    , Scheme(..)
    , scmParams
    , scmBody
    , Id
    , idstr
    , Const(..)
    , Pat(..)
    , Expr'(..)
    , Expr
    , Def
    , ConstructorDefs(..)
    , TypeDef(..)
    , Program(..)
    )
where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List
import Data.Bifunctor
import Control.Lens (makeLenses)

import Misc
import SrcPos
import FreeVars
import NonEmpty

type Id = WithPos String

idstr :: Id -> String
idstr = unpos

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
    -- TODO: Not curried yet! Handle that in the parser instead, so that AST
    -- matches closer to what's actually parsed. That will improve error msgs
    | TFun Type Type
    deriving (Show, Eq, Ord)

data Scheme = Forall
    { _scmParams :: (Set TVar)
    , _scmBody :: Type
    } deriving (Show, Eq)
makeLenses ''Scheme

data Pat
    = PConstruction SourcePos Id [Pat]
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

data Expr'
    = Lit Const
    | Var Id
    | App Expr
          Expr
    | If Expr
         Expr
         Expr
    -- TODO: Not curried yet! Handle that in the parser instead, so that AST
    -- matches closer to what's actually parsed. That will improve error msgs
    | Fun Id Expr
    | Let (NonEmpty Def)
          Expr
    | TypeAscr Expr Type
    | Match Expr
            (NonEmpty (Pat, Expr))
    | FunMatch (NonEmpty (Pat, Expr))
    | Constructor Id
    deriving (Show, Eq)

type Expr = WithPos Expr'

type Def = (Id, (Maybe (WithPos Scheme), Expr))

newtype ConstructorDefs = ConstructorDefs (Map String [Type])
    deriving (Show, Eq)

data TypeDef = TypeDef String [Id] ConstructorDefs
    deriving (Show, Eq)

data Program = Program [Def] [TypeDef]
    deriving (Show, Eq)

instance FreeVars Def Id where
    freeVars (name, (_, body)) = Set.delete name (freeVars body)

instance FreeVars Expr Id where
    freeVars = fvExpr

fvExpr :: Expr -> Set Id
fvExpr = onPosd $ \case
    Lit _ -> Set.empty
    Var x -> Set.singleton x
    App f a -> fvApp f a
    If p c a -> fvIf p c a
    Fun p b -> fvFun p b
    Let bs e ->
        fvLet (Set.fromList (fromList1 (map1 fst bs)), map1 (snd . snd) bs) e
    TypeAscr e _ -> freeVars e
    Match e cs -> fvMatch e (fromList1 cs)
    FunMatch cs -> fvCases (fromList1 cs)
    Constructor _ -> Set.empty

instance Pattern Pat Id where
    patternBoundVars = bvPat

bvPat :: Pat -> Set Id
bvPat = \case
    PConstruction _ _ ps -> Set.unions (map bvPat ps)
    PVar x -> Set.singleton x

instance HasPos Pat where
    getPos = \case
        PConstruction p _ _ -> p
        PVar v -> getPos v

instance Pretty Program where
    pretty' = prettyProg
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

prettyProg :: Int -> Program -> String
prettyProg d (Program defs tdefs) =
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
    in unlines (map prettyDef defs ++ map pretty tdefs)

prettyTypeDef :: Int -> TypeDef -> String
prettyTypeDef d (TypeDef name params constrs) = concat
    [ "(type "
    , if null params then name else "(" ++ name ++ spcPretty params ++ ")"
    , indent (d + 2) ++ pretty' (d + 2) constrs
    , ")"
    ]

prettyConstructorDefs :: Int -> ConstructorDefs -> String
prettyConstructorDefs d (ConstructorDefs cs) = intercalate
    ("\n" ++ indent d)
    (map prettyConstrDef (Map.toList cs))
  where
    prettyConstrDef = \case
        (c, []) -> c
        (c, ts) -> concat ["(", c, " ", spcPretty ts, ")"]

prettyExpr' :: Int -> Expr' -> String
prettyExpr' d = \case
    Lit l -> pretty l
    Var v -> idstr v
    App f x -> concat
        [ "(" ++ pretty' (d + 1) f ++ "\n"
        , indent (d + 1) ++ pretty' (d + 1) x ++ ")"
        ]
    If pred cons alt -> concat
        [ "(if " ++ pretty' (d + 4) pred ++ "\n"
        , indent (d + 4) ++ pretty' (d + 4) cons ++ "\n"
        , indent (d + 2) ++ pretty' (d + 2) alt ++ ")"
        ]
    Fun param body ->
        concat
            [ "(fun "
            , idstr param
            , "\n"
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
        prettyDef d = \case
            (name, (Just scm, body)) -> concat
                [ "[: " ++ pretty' (d + 3) name ++ "\n"
                , indent (d + 3) ++ pretty' (d + 3) scm ++ "\n"
                , indent (d + 1) ++ pretty' (d + 1) body ++ "]"
                ]
            (name, (Nothing, body)) -> concat
                [ "[" ++ pretty' (d + 1) name ++ "\n"
                , indent (d + 1) ++ pretty' (d + 1) body ++ "]"
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
    Constructor c -> pretty c

prettyPat :: Pat -> String
prettyPat = \case
    PConstruction _ c ps -> concat ["(", idstr c, " ", spcPretty ps, ")"]
    PVar v -> idstr v

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
    Ast.TConst c ts -> case ts of
        [] -> c
        ts -> concat ["(", c, " ", spcPretty ts, ")"]

prettyTFun :: Type -> Type -> String
prettyTFun a b =
    let
        (bParams, bBody) = f b
        f = \case
            TFun a' b' -> first (a' :) (f b')
            t -> ([], t)
    in concat
        ["(Fun ", pretty a, " ", spcPretty bParams, " ", pretty bBody, ")"]

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
    TVExplicit v -> idstr v
    TVImplicit n -> "#" ++ show n

spcPretty :: Pretty a => [a] -> String
spcPretty = unwords . map pretty
