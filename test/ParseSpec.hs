{-# LANGUAGE NumDecimals #-}

module ParseSpec where

import Text.Parsec hiding (parse)
import Test.Hspec
import Test.QuickCheck

import Ast
import Pretty
import Parse

spec :: Spec
spec = do
  describe "parse, few" $
    it "parses a program to an AST, and is the inverse of pretty. Runs a few times." $
    withMaxSuccess 1e3 (\progAst -> parse "spec" (pretty progAst) == Right progAst)
  describe "parse, many" $
    it ": Same as above, but many times." $
    withMaxSuccess 6e4 (\progAst -> parse "spec" (pretty progAst) == Right progAst)
