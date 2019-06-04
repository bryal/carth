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
              5e4
              (\progAst -> parse "spec" (pretty progAst) == Right progAst)
