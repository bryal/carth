{-# LANGUAGE LambdaCase #-}

module Main where

import Parse
import Check
import Interp
import Data.Composition
import System.Environment
import System.Exit

main :: IO ()
main = do
  args <- getArgs
  case args of
    file:[] -> interpretFile file
    _ -> usage

interpretFile :: FilePath -> IO ()
interpretFile file = readFile file >>= parse' file >>= typecheck' >>= interpret'
  where parse' = handleErr "Syntax error" .* parse
        typecheck' = handleErr "Type error" . typecheck
        interpret' = handleErr "Interpretation error" . interpret
        handleErr title =
          either (\err -> putStrLn title >> putStrLn (show err) >> exitFailure) pure

usage :: IO ()
usage = putStrLn "Usage: carth SRC-FILE" >> exitFailure
