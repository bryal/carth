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
    , FreeVars(..)
    , mainType
    )
where

import Data.String
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List
import Control.Lens (makeLenses)

import Misc
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
    deriving (Show, Eq)

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
    boundVars (name, _) = Set.singleton name
instance FreeVars Expr Id where
    freeVars = fvExpr
instance FreeVars Pat Id where
    freeVars = const Set.empty
    boundVars = bvPat

fvExpr :: Expr -> Set Id
fvExpr = \case
    Lit _ -> Set.empty
    Var x -> Set.singleton x
    App f a -> Set.unions (map freeVars [f, a])
    If p c a -> Set.unions (map freeVars [p, c, a])
    Fun p b -> Set.delete p (freeVars b)
    Let bs e ->
        Set.difference (Set.union (freeVars e) (freeVars bs)) (boundVars bs)
    TypeAscr e _ -> freeVars e
    Match _ _ -> undefined
    FunMatch _ -> undefined
    Constructor _ -> undefined

bvPat :: Pat -> Set Id
bvPat = \case
    PConstructor _ -> Set.empty
    PConstruction _ ps -> Set.unions (map freeVars (nonEmptyToList ps))
    PVar var -> Set.singleton var

instance Pretty Program            where pretty' = prettyProg
instance Pretty TypeDef            where pretty' = prettyTypeDef
instance Pretty TypeDefConstructor where pretty' _ = prettyTypeDefConstr
instance Pretty Expr               where pretty' = prettyExpr
instance Pretty Id                 where pretty' _ (Id s) = s
instance Pretty Pat                where pretty' _ = prettyPat
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
                [ replicate d ' '
                , "(define: "
                , pretty name
                , "\n"
                , replicate (d + 4) ' '
                , pretty' (d + 4) scm
                , "\n"
                , replicate (d + 2) ' '
                , pretty' (d + 2) body
                , ")"
                ]
            (name, (Nothing, body)) -> concat
                [ replicate d ' '
                , "(define "
                , pretty name
                , "\n"
                , replicate (d + 2) ' '
                , pretty' (d + 2) body
                , ")"
                ]
    in unlines (map prettyDef allDefs ++ map pretty tdefs)

prettyTypeDef :: Int -> TypeDef -> String
prettyTypeDef d (TypeDef name params constrs) = concat
    [ "(type "
    , if null params
        then name
        else "(" ++ name ++ precalate " " (map pretty params) ++ ")"
    , precalate ("\n" ++ replicate (d + 2) ' ') (map pretty constrs)
    , ")"
    ]

prettyTypeDefConstr :: TypeDefConstructor -> String
prettyTypeDefConstr (TypeDefConstructor c ts) = case ts of
    [] -> c
    _ -> concat ["(", c, precalate " " (map pretty ts), ")"]

prettyExpr :: Int -> Expr -> String
prettyExpr d = \case
    Lit l -> pretty l
    Var (Id v) -> v
    App f x -> concat
        [ "("
        , pretty' (d + 1) f
        , "\n"
        , replicate (d + 1) ' '
        , pretty' (d + 1) x
        , ")"
        ]
    If pred cons alt -> concat
        [ "(if "
        , pretty' (d + 4) pred
        , "\n"
        , replicate (d + 4) ' '
        , pretty' (d + 4) cons
        , "\n"
        , replicate (d + 2) ' '
        , pretty' (d + 2) alt
        , ")"
        ]
    Fun (Id param) body ->
        concat
            [ "(fun "
            , param
            , "\n"
            , replicate (d + 2) ' '
            , pretty' (d + 2) body
            , ")"
            ]
    Let binds body -> concat
        [ "(let ["
        , intercalate1
            ("\n" ++ replicate (d + 6) ' ')
            (map1 (prettyDef (d + 6)) binds)
        , "]\n"
        , replicate (d + 2) ' ' ++ pretty' (d + 2) body
        , ")"
        ]
      where
        prettyDef d = \case
            (name, (Just scm, body)) -> concat
                [ "[: "
                , pretty' (d + 3) name
                , "\n"
                , replicate (d + 3) ' '
                , pretty' (d + 3) scm
                , "\n"
                , replicate (d + 1) ' '
                , pretty' (d + 1) body
                , "]"
                ]
            (name, (Nothing, body)) -> concat
                [ "["
                , pretty' (d + 1) name
                , "\n"
                , replicate (d + 1) ' '
                , pretty' (d + 1) body
                , "]"
                ]
    TypeAscr e t ->
        concat ["(: ", pretty' (d + 3) e, "\n", pretty' (d + 3) t, ")"]
    Match e cs -> concat
        [ "(match "
        , pretty' (d + 7) e
        , precalate1
            ("\n" ++ replicate (d + 2) ' ')
            (map1 (prettyBracketPair (d + 2)) cs)
        , ")"
        ]
    FunMatch cs -> concat
        [ "(fun-match"
        , precalate1
            ("\n" ++ replicate (d + 2) ' ')
            (map1 (prettyBracketPair (d + 2)) cs)
        , ")"
        ]
    Constructor c -> c

prettyPat :: Pat -> String
prettyPat = \case
    PConstructor c -> c
    PConstruction c ps ->
        concat ["(", c, precalate " " (nonEmptyToList (map1 pretty ps)), ")"]
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
