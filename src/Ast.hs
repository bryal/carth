{-# LANGUAGE LambdaCase #-}

module Ast (Id (..), Pat (..), Expr (..), Program (..)) where

import NonEmpty
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Control.Monad
import Test.QuickCheck.Gen
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Modifiers

newtype Id = Id String
  deriving (Show, Eq, Ord)

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
  | Let (NonEmpty (Id, Expr)) Expr
  | Match Expr (NonEmpty (Pat, Expr))
  | FunMatch (NonEmpty (Pat, Expr))
  | Constructor String
  deriving (Show, Eq)

type Defs = Map Id Expr

data Program = Program Expr Defs
  deriving (Show, Eq)

instance Arbitrary Program where
  arbitrary = liftM2 Program arbitrary (fmap Map.fromList (shortList arbitrary))

instance Arbitrary Expr where
  arbitrary = frequency [ (5, pure Unit)
                        , (15, fmap Int arbitrary)
                        , (15, fmap Double arbitrary)
                        , (8, fmap (Str . getUnicodeString) arbitrary)
                        , (5, fmap Bool arbitrary)
                        , (30, fmap Var arbitrary)
                        , (8, applyArbitrary2 App)
                        , (5, applyArbitrary3 If)
                        , (5, applyArbitrary2 Fun)
                        , (5, applyArbitrary2 Let)
                        , (4, applyArbitrary2 Match)
                        , (4, fmap FunMatch arbitrary)
                        , (15, fmap Constructor arbitraryConstructor) ]

instance Arbitrary Pat where
  arbitrary = frequency [ (3, fmap PConstructor arbitraryConstructor)
                        , (1, liftM2 PConstruction arbitraryConstructor arbitrary)
                        , (3, fmap PVar arbitrary)]

instance Arbitrary Id where
  arbitrary = do
    first <- frequency [ (26, choose ('a', 'z')), (4, elements ['_', '-', '+', '?']) ]
    rest <- arbitraryRestIdent
    pure (Id (first:rest))

instance Arbitrary a => Arbitrary (NonEmpty a) where
  arbitrary = liftM2 (:|) arbitrary (shortList arbitrary)

arbitraryConstructor :: Gen String
arbitraryConstructor = liftM2 (:) (choose ('A', 'Z')) arbitraryRestIdent

arbitraryRestIdent :: Gen String
arbitraryRestIdent = shortList c
  where c = frequency [ (26, choose ('a', 'z'))
                      , (26, choose ('A', 'Z'))
                      , (4, elements ['_', '-', '+', '?']) ]

shortList :: Arbitrary a => Gen a -> Gen [a]
shortList gen = choose (0, 8) >>= flip vectorOf gen
