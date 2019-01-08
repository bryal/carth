module ParseSpec where

import Text.Parsec hiding (parse)
import Test.Hspec
import Test.QuickCheck

import Ast
import Parse

spec :: Spec
spec = describe "parse" $ do
  it "parses a program to an AST, and is the inverse of pretty"
     (property (\progAst -> parse "spec" (pretty progAst) == Right progAst))
