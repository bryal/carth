{-# LANGUAGE NumDecimals #-}

module ParseSpec where

import Text.Parsec hiding (parse)
import Test.Hspec
import Test.QuickCheck

import Misc
import Ast
import Parse

spec :: Spec
spec = do
    describe "parse inverse of pretty"
        $ it
              "Parsing a pretty printed program should return the original program"
        $ withMaxSuccess
              4e5
              (\progAst -> parse "spec" (pretty progAst) == Right progAst)
