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
    , Pat' (..)
    , Pat
    , Expr'(..)
    , Expr
    , Def
    , ConstructorDefs(..)
    , TypeDef(..)
    , Program(..)
    , mainType
    )
where

import Data.String
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List
import Control.Lens (makeLenses)

import Misc
import SrcPos
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

data Pat'
    -- TODO: Should we really be discriminating between unapplied constructors
    --       and constructions with >0 arguments at this level? Consider
    --       `PConstructor "Foo"` and `PConstruction "Foo" []`.
    = PConstructor String
    | PConstruction String
                    (NonEmpty Pat)
    | PVar Id
    deriving (Show, Eq)

type Pat = WithPos Pat'

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

type Expr = WithPos Expr'

type Def = (Id, (Maybe (WithPos Scheme), Expr))

newtype ConstructorDefs = ConstructorDefs (Map String [Type])
    deriving (Show, Eq)

data TypeDef = TypeDef String [Id] ConstructorDefs
    deriving (Show, Eq)

data Program = Program (Maybe (WithPos Scheme), Expr) [Def] [TypeDef]
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
bvPat = onPosd $ \case
    PConstructor _ -> Set.empty
    PConstruction _ ps -> Set.unions (map1 bvPat ps)
    PVar x -> Set.singleton x

instance Pretty Program            where pretty' = prettyProg
instance Pretty ConstructorDefs    where pretty' = prettyConstructorDefs
instance Pretty TypeDef            where pretty' = prettyTypeDef
instance Pretty Expr'              where pretty' = prettyExpr'
instance Pretty Id                 where pretty' _ (Id s) = s
instance Pretty Pat'               where pretty' _ = prettyPat'
instance Pretty Const              where pretty' _ = prettyConst
instance Pretty Scheme             where pretty' _ = prettyScheme
instance Pretty Type               where pretty' _ = prettyType
instance Pretty TPrim              where pretty' _ = prettyTPrim
instance Pretty TVar               where pretty' _ = prettyTVar

prettyProg :: Int -> Program -> String
prettyProg d (Program main defs tdefs) =
    let
        allDefs = (Id "main", main) : defs
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
    in unlines (map prettyDef allDefs ++ map pretty tdefs)

prettyTypeDef :: Int -> TypeDef -> String
prettyTypeDef d (TypeDef name params constrs) = concat
    [ "(type "
    , if null params
        then name
        else "(" ++ name ++ precalate " " (map pretty params) ++ ")"
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
        (c, ts) -> concat ["(", c, precalate " " (map pretty ts), ")"]

prettyExpr' :: Int -> Expr' -> String
prettyExpr' d = \case
    Lit l -> pretty l
    Var (Id v) -> v
    App f x -> concat
        [ "(" ++ pretty' (d + 1) f ++ "\n"
        , indent (d + 1) ++ pretty' (d + 1) x ++ ")"
        ]
    If pred cons alt -> concat
        [ "(if " ++ pretty' (d + 4) pred ++ "\n"
        , indent (d + 4) ++ pretty' (d + 4) cons ++ "\n"
        , indent (d + 2) ++ pretty' (d + 2) alt ++ ")"
        ]
    Fun (Id param) body ->
        concat ["(fun ", param, "\n", indent (d + 2), pretty' (d + 2) body, ")"]
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
    Constructor c -> c

prettyPat' :: Pat' -> String
prettyPat' = \case
    PConstructor c -> c
    PConstruction c ps ->
        concat ["(", c, precalate " " (fromList1 (map1 pretty ps)), ")"]
    PVar (Id v) -> v

prettyConst :: Const -> String
prettyConst = \case
    Unit -> "unit"
    Int n -> show n
    Double x -> show x
    Char c -> showChar' c
    Str s -> '"' : (s >>= showChar'') ++ "\""
    Bool b -> if b then "true" else "false"

prettyScheme :: Scheme -> String
prettyScheme (Forall ps t) = concat
    [ "(forall [" ++ intercalate " " (map pretty (Set.toList ps)) ++ "] "
    , pretty t ++ ")"
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
