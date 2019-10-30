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
    describe "parse" $ it "is the inverse of pretty" $ withMaxSuccess
        1e4
        (\progAst -> parse "spec" (pretty progAst) == Right progAst)
