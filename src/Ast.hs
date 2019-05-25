{-# LANGUAGE LambdaCase, TypeSynonymInstances, FlexibleInstances
           , MultiParamTypeClasses #-}

module Ast
    ( Id(..)
    , Const(..)
    , Pat(..)
    , Expr(..)
    , Def
    , Program(..)
    , reserveds
    , FreeVars(..)
    )
where

import Control.Monad
import Data.String
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import Test.QuickCheck.Modifiers
import qualified Data.Set as Set
import Data.Set (Set)

import Misc
import NonEmpty

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
    | Match Expr
            (NonEmpty (Pat, Expr))
    | FunMatch (NonEmpty (Pat, Expr))
    | Constructor String
    deriving (Show, Eq)

type Def = (Id, Expr)

data Program =
    Program Expr
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
            , (4, applyArbitrary2 Match)
            , (4, fmap FunMatch arbitrary)
            , (15, fmap Constructor arbitraryConstructor)
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
            [ (3, fmap PConstructor arbitraryConstructor)
            , (1, liftM2 PConstruction arbitraryConstructor arbitrary)
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

arbitraryConstructor :: Gen String
arbitraryConstructor = liftM2 (:) (choose ('A', 'Z')) arbitraryRestIdent

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
    ["define", "unit", "true", "false", "fun-match", "match", "if", "fun", "let"]

instance FreeVars Def Id where
    freeVars (name, body) = Set.delete name (freeVars body)
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
        Set.union (Set.difference (freeVars e) (boundVars bs)) (freeVars bs)
    Match e cs ->
        Set.union (freeVars e) (Set.difference (fvClauses cs) (bvClauses cs))
    FunMatch cs -> Set.difference (fvClauses cs) (bvClauses cs)
    Constructor _ -> Set.empty
  where
    fvClauses = foldl (\acc c -> Set.union acc (freeVars (snd c))) Set.empty
    bvClauses = Set.unions . map (freeVars . fst) . nonEmptyToList

bvPat :: Pat -> Set Id
bvPat = \case
    PConstructor _ -> Set.empty
    PConstruction _ ps -> Set.unions (map freeVars (nonEmptyToList ps))
    PVar var -> Set.singleton var
