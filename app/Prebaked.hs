module Prebaked (readCompilerVersion) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Lift(..))
import Data.Maybe
import qualified Text.Megaparsec as M
import qualified Text.Megaparsec.Char as MC
import qualified Text.Megaparsec.Char.Lexer as ML
import Data.Void

type Parser = M.Parsec Void String

readCompilerVersion :: Q Exp
readCompilerVersion = do
    s <- runIO (readFile "carth.cabal")
    let (_, major, minor, patch) = head (catMaybes (map (M.parseMaybe pversion) (lines s)))
    lift (major, minor, patch)

pversion :: Parser (Int, Int, Int, Int)
pversion = do
    MC.string "version:" >> MC.space
    a <- num
    b <- dot >> num
    c <- dot >> num
    d <- dot >> num
    pure (a, b, c, d)
  where
    num = ML.decimal
    dot = MC.char '.'
