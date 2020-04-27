module Prebaked (readCompilerVersion, getCommit) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Lift(..), qAddDependentFile)
import Data.Maybe
import qualified Text.Megaparsec as M
import qualified Text.Megaparsec.Char as MC
import qualified Text.Megaparsec.Char.Lexer as ML
import Data.Void
import System.Process

type Parser = M.Parsec Void String

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

readCompilerVersion :: Q Exp
readCompilerVersion = do
    s <- runIO (readFile "package.yaml")
    let (_, major, minor, patch) =
            head (catMaybes (map (M.parseMaybe pversion) (lines s)))
    lift (major, minor, patch)

getCommit :: Q Exp
getCommit =
    qAddDependentFile ".git/index"
        >> runIO
            (do
                c <- fmap (head . lines)
                    $ readProcess "git" ["rev-parse", "--short", "HEAD"] ""
                d <- fmap (head . lines)
                    $ readProcess "git" ["show", "-s", "--format=%ci", c] ""
                pure (c, d)
            )
        >>= lift
