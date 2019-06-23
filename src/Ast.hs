{-# LANGUAGE LambdaCase, TypeSynonymInstances, FlexibleInstances
           , MultiParamTypeClasses, TemplateHaskell #-}

module Ast
    ( TVar(..)
    , TConst(..)
    , Type(..)
    , Scheme(..)
    , scmParams
    , scmBody
    , Id(..)
    , Const(..)
    , Pat(..)
    , Expr(..)
    , Def
    , Program(..)
    , reserveds
    , FreeVars(..)
    , mainType
    )
where

import Control.Monad
import Data.String
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import Test.QuickCheck.Modifiers
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List
import Control.Lens (makeLenses)

import Misc
import NonEmpty

data TVar
    = TVExplicit String
    | TVImplicit Int
    deriving (Show, Eq, Ord)

data TConst
    = TUnit
    | TInt
    | TDouble
    | TChar
    | TStr
    | TBool
    deriving (Show, Eq, Ord)

data Type
    = TVar TVar
    | TConst TConst
    | TFun Type
           Type
    deriving (Show, Eq)

mainType :: Type
mainType = TFun (TConst TUnit) (TConst TUnit)

data Scheme = Forall
    { _scmParams :: (Set TVar)
    , _scmBody :: Type
    } deriving (Show, Eq)
makeLenses ''Scheme

newtype Id =
    Id String
    deriving (Eq, Ord)

instance Show Id where
    show (Id x) = x

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

data Program =
    Program (Maybe Scheme, Expr)
            [Def]
    deriving (Show, Eq)

instance IsString Id where
    fromString = Id

instance Arbitrary Program where
    arbitrary = do
        main <- arbitrary
        defs <- choose (0, 4) >>= flip vectorOf arbitrary
        pure (Program main defs)
    shrink (Program main defs) =
        [Program main' defs' | (main', defs') <- shrink (main, defs)]

instance Arbitrary Expr where
    arbitrary =
        frequency
            [ (5, pure (Lit Unit))
            , (15, fmap (Lit . Int) arbitrary)
            , (15, fmap (Lit . Double) arbitrary)
            , (8, fmap (Lit . Str . getPrintableString) arbitrary)
            , (5, fmap (Lit . Bool) arbitrary)
            , (5, fmap (Lit . Char) arbitraryChar)
            , (30, fmap Var arbitrary)
            , (8, applyArbitrary2 App)
            , (5, applyArbitrary3 If)
            , (5, applyArbitrary2 Fun)
            , (5, applyArbitrary2 Let)
            , (1, applyArbitrary2 TypeAscr)
            , (4, applyArbitrary2 Match)
            , (4, fmap FunMatch arbitrary)
            , (15, fmap Constructor arbitraryBig)
            ]
      where
        arbitraryChar =
            oneof
                [ choose ('a', 'z')
                , choose ('A', 'Z')
                , choose ('0', '9')
                , elements ['+', '-', '?', '(', ']', '#']
                , elements ['\n', '\t', '\0', '\a']
                ]
    shrink =
        \case
            App f x ->
                [Lit Unit, f, x] ++ [App f' x' | (f', x') <- shrink (f, x)]
            If p c a ->
                [Lit Unit, p, c, a] ++
                [If p' c' a' | (p', c', a') <- shrink (p, c, a)]
            Fun p b -> [Lit Unit, b] ++ [Fun p' b' | (p', b') <- shrink (p, b)]
            Let bs x ->
                [Lit Unit, x] ++ [Let bs' x' | (bs', x') <- shrink (bs, x)]
            Match e cs ->
                [Lit Unit, e] ++ [Match e' cs' | (e', cs') <- shrink (e, cs)]
            FunMatch cs -> Lit Unit : map FunMatch (shrink cs)
            _ -> []

instance Arbitrary Pat where
    arbitrary =
        frequency
            [ (3, fmap PConstructor arbitraryBig)
            , (1, liftM2 PConstruction arbitraryBig arbitrary)
            , (3, fmap PVar arbitrary)
            ]
    shrink =
        \case
            PConstruction c ps ->
                PConstructor c : map (PConstruction c) (shrink ps)
            _ -> []

instance Arbitrary Id where
    arbitrary = do
        let first =
                frequency [(26, choose ('a', 'z')), (4, elements ['_', '?'])]
        firsts <-
            frequency
                [ (10, fmap pure first)
                , ( 1
                  , liftM2
                        (\a b -> a : [b])
                        (elements ['-', '+'])
                        (choose ('a', 'z')))
                ]
        rest <- arbitraryRestIdent
        let id = firsts ++ rest
        if elem id reserveds
            then arbitrary
            else pure (Id id)

instance Arbitrary Scheme where
    arbitrary = applyArbitrary2 Forall

instance Arbitrary Type where
    arbitrary = frequency
        [ (1, fmap TVar arbitrary)
        , (4, fmap TConst arbitrary)
        , (2, applyArbitrary2 TFun) ]

instance Arbitrary TVar where
    arbitrary = fmap (\(Id s) -> TVExplicit s) arbitrary

instance Arbitrary TConst where
    arbitrary = elements [TUnit, TInt, TDouble, TChar, TStr, TBool ]

arbitraryBig :: Gen String
arbitraryBig = do
    c <- liftM2 (:) (choose ('A', 'Z')) arbitraryRestIdent
    if elem c reserveds then arbitraryBig else pure c

arbitraryRestIdent :: Gen String
arbitraryRestIdent = choose (0, 8) >>= flip vectorOf c
  where
    c = frequency
        [ (26, choose ('a', 'z'))
        , (26, choose ('A', 'Z'))
        , (4, elements ['_', '-', '+', '?'])
        ]

reserveds :: [String]
reserveds =
    [ ":"
    , "Fun"
    , "define"
    , "define:"
    , "forall"
    , "unit"
    , "true"
    , "false"
    , "fun-match"
    , "match"
    , "if"
    , "fun"
    , "let"
    ]

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

instance Pretty Program where
    pretty' = prettyProg

instance Pretty Expr where
    pretty' = prettyExpr

instance Pretty Id where
    pretty' _ (Id s) = s

instance Pretty Pat where
    pretty' _ = prettyPat

instance Pretty Const where
    pretty' _ = prettyConst

instance Pretty Scheme where
    pretty' _ = prettyScheme

instance Pretty Type where
    pretty' _ = prettyType

instance Pretty TConst where
    pretty' _ = prettyTConst

instance Pretty TVar where
    pretty' _ = prettyTVar

prettyProg :: Int -> Program -> String
prettyProg d (Program main defs) =
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
    in unlines (map prettyDef allDefs)

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
        , "\n"
        , replicate (d + 2) ' '
        , intercalate1
            ("\n" ++ replicate (d + 2) ' ')
            (map1 (prettyBracketPair (d + 2)) cs)
        , ")"
        ]
    FunMatch cs -> concat
        [ "(fun-match\n"
        , replicate (d + 2) ' '
        , intercalate1
            ("\n" ++ replicate (d + 2) ' ')
            (map1 (prettyBracketPair (d + 2)) cs)
        , ")"
        ]
    Constructor c -> c

prettyPat :: Pat -> String
prettyPat = \case
    PConstructor c -> c
    PConstruction c ps -> concat
        ["(", c, " ", intercalate " " (nonEmptyToList (map1 pretty ps)), ")"]
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
    Ast.TConst c -> pretty c
    Ast.TFun a b -> concat ["(Fun ", pretty a, " ", pretty b, ")"]

prettyTConst :: TConst -> String
prettyTConst = \case
    TUnit -> "Unit"
    TInt -> "Int"
    TDouble -> "Double"
    TChar -> "Char"
    TStr -> "Str"
    TBool -> "Bool"

prettyTVar :: TVar -> String
prettyTVar = \case
    TVExplicit v -> v
    TVImplicit n -> "#" ++ show n
