{-# LANGUAGE NumDecimals #-}

module ParseSpec where

import Test.Hspec
import Test.QuickCheck

import Misc
import Ast
import Parse
import Arbitrary


spec :: Spec
spec = do
    describe "parse inverse of pretty"
        $ it
            "Parsing a pretty printed program should return the original program"
        $ withMaxSuccess
            1e5
            (\progAst -> parse "spec" (pretty progAst) == Right progAst)
