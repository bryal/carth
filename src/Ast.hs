{-# LANGUAGE LambdaCase #-}

module Ast (Id (..), Pat (..), Expr (..), Def, Program (..), reserveds) where

import NonEmpty
import Data.String
import Control.Monad
import Test.QuickCheck.Gen
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Modifiers

newtype Id = Id String
  deriving (Eq, Ord)

instance Show Id where
  show (Id x) = x

data Pat
  = PConstructor String
  | PConstruction String (NonEmpty Pat)
  | PVar Id
  deriving (Show, Eq)

data Expr
  = Unit
  | Int Int
  | Double Double
  | Str String
  | Bool Bool
  | Var Id
  | App Expr Expr
  | If Expr Expr Expr
  | Fun Id Expr
  | Let (NonEmpty Def) Expr
  | Match Expr (NonEmpty (Pat, Expr))
  | FunMatch (NonEmpty (Pat, Expr))
  | Constructor String
  | Char Char
  deriving (Show, Eq)

type Def = (Id, Expr)

data Program = Program Expr [Def]
  deriving (Show, Eq)

instance IsString Id where
  fromString = Id

instance Arbitrary Program where
  arbitrary = do
    main <- arbitrary
    defs <- choose (0, 4) >>= flip vectorOf arbitrary
    pure (Program main defs)
  shrink (Program main defs) = [Program main' defs' | (main', defs') <- shrink (main, defs)]

instance Arbitrary Expr where
  arbitrary = frequency [ (5, pure Unit)
                        , (15, fmap Int arbitrary)
                        , (15, fmap Double arbitrary)
                        , (8, fmap (Str . getPrintableString) arbitrary)
                        , (5, fmap Bool arbitrary)
                        , (30, fmap Var arbitrary)
                        , (8, applyArbitrary2 App)
                        , (5, applyArbitrary3 If)
                        , (5, applyArbitrary2 Fun)
                        , (5, applyArbitrary2 Let)
                        , (4, applyArbitrary2 Match)
                        , (4, fmap FunMatch arbitrary)
                        , (15, fmap Constructor arbitraryConstructor)
                        , (5, fmap Char arbitraryChar)]
    where arbitraryChar = oneof [ choose ('a', 'z')
                                , choose ('A', 'Z')
                                , choose ('0', '9')
                                , elements ['+', '-', '?', '(', ']', '#']
                                , elements ['\n', '\t', '\0', '\a'] ]
  shrink = \case
    App f x -> [Unit, f, x] ++ [App f' x' | (f', x') <- shrink (f, x)]
    If p c a -> [Unit, p, c, a] ++ [If p' c' a' | (p', c', a') <- shrink (p, c, a)]
    Fun p b -> [Unit, b] ++ [Fun p' b' | (p', b') <- shrink (p, b)]
    Let bs x -> [Unit, x] ++ [Let bs' x' | (bs', x') <- shrink (bs, x)]
    Match e cs -> [Unit, e] ++ [Match e' cs' | (e', cs') <- shrink (e, cs)]
    FunMatch cs -> Unit : map FunMatch (shrink cs)
    _ -> []

instance Arbitrary Pat where
  arbitrary = frequency [ (3, fmap PConstructor arbitraryConstructor)
                        , (1, liftM2 PConstruction arbitraryConstructor arbitrary)
                        , (3, fmap PVar arbitrary)]
  shrink = \case
    PConstruction c ps -> PConstructor c : map (PConstruction c) (shrink ps)
    _ -> []

instance Arbitrary Id where
  arbitrary = do
    let first = frequency [ (26, choose ('a', 'z')), (4, elements ['_', '?']) ]
    firsts <- frequency [ (10, fmap pure first)
                        , (1, liftM2 (\a b -> a:[b])
                                     (elements ['-', '+'])
                                     (choose ('a', 'z'))) ]
    rest <- arbitraryRestIdent
    let id = firsts ++ rest
    if elem id reserveds
      then arbitrary
      else pure (Id id)

arbitraryConstructor :: Gen String
arbitraryConstructor = liftM2 (:) (choose ('A', 'Z')) arbitraryRestIdent

arbitraryRestIdent :: Gen String
arbitraryRestIdent = choose (0, 8) >>= flip vectorOf c
  where c = frequency [ (26, choose ('a', 'z'))
                      , (26, choose ('A', 'Z'))
                      , (4, elements ['_', '-', '+', '?']) ]

reserveds :: [String]
reserveds =
  [ "define"
  , "unit"
  , "true"
  , "false"
  , "fun-match"
  , "match"
  , "if"
  , "fun"
  , "let" ]
