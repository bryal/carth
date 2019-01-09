{-# LANGUAGE LambdaCase #-}

module Ast (Id (..), Expr (..), Program (..), pretty) where

import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Control.Monad
import Test.QuickCheck

newtype Id = Id String
  deriving (Show, Eq, Ord)

data Expr
  = Unit
  | Int Int
  | Double Double
  | Str String
  | Bool Bool
  | Var Id
  | App Expr Expr
  | If Expr Expr Expr
  | Lam Id Expr
  | Let [(Id, Expr)] Expr
  deriving (Show, Eq)

type Defs = Map Id Expr

data Program = Program Expr Defs
  deriving (Show, Eq)

instance Arbitrary Program where
  arbitrary = applyArbitrary2 Program

instance Arbitrary Expr where
  arbitrary = frequency [ (5, pure Unit)
                        , (15, fmap Int arbitrary)
                        , (15, fmap Double arbitrary)
                        , (8, fmap (Str . getUnicodeString) arbitrary)
                        , (5, fmap Bool arbitrary)
                        , (30, fmap Var arbitrary)
                        , (20, applyArbitrary2 App)
                        , (10, applyArbitrary3 If)
                        , (10, applyArbitrary2 Lam)
                        , (10, arbitraryLet) ]
    where arbitraryLet :: Gen Expr
          arbitraryLet = do
            n <- choose (0, 6)
            bindings <- vectorOf n (applyArbitrary2 (,))
            body <- arbitrary
            pure (Let bindings body)

instance Arbitrary Id where
  arbitrary = fmap Id (choose (1, 15) >>= flip vectorOf c)
    where c = frequency [ (26, choose ('a', 'z'))
                        , (26, choose ('A', 'Z'))
                        , (4, elements ['_', '-', '+', '?']) ]

-- variable def of name and val (expr)

-- def of either function/variable or data-type

-- program of defs, main

-- Pretty print an AST
pretty :: Expr -> String
pretty = pretty' 0

-- Pretty print starting at indentation depth `d`
pretty' :: Int -> Expr -> String
pretty' d = \case
  Unit -> "unit"
  Int n -> show n
  Double x -> show x
  Str s -> '"' : s ++ "\""
  Bool b -> if b then "true" else "false"
  Var (Id v) -> v
  App f x ->
    concat [ "(", pretty' (d + 1) f, "\n"
           , replicate (d + 1) ' ',  pretty' (d + 1) x, ")" ]
  If pred cons alt ->
    concat [ "(if ", pretty' (d + 4) pred, "\n"
           , replicate (d + 4) ' ', pretty' (d + 4) cons, "\n"
           , replicate (d + 2) ' ', pretty' (d + 2) alt, ")" ]
  Lam (Id param) body ->
    concat [ "(lambda [", param, "]", "\n"
           , replicate (d + 8) ' ', pretty' (d + 8) body, ")" ]
  Let binds body ->
    concat [ "(let ["
           , intercalate ("\n" ++ replicate (d + 6) ' ')
                         (map (prettyBind (d + 6)) binds)
           , "]\n"
           , replicate (d + 2) ' ' ++ pretty' (d + 2) body, ")" ]
  where prettyBind d (Id var, val) =
          concat [ "[", var, "\n"
                 , replicate (d + 1) ' ', pretty' (d + 1) val, "]" ]
