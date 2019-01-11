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
  describe "parse" $
    it "parses a program to an AST, and is the inverse of pretty" $
    withMaxSuccess 200 (\progAst -> parse "spec" (pretty progAst) == Right progAst)
