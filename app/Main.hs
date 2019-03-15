{-# LANGUAGE LambdaCase #-}

module Main where

import Parse
import Check
import Interp
import Data.Composition
import Data.Functor
import System.Environment
import System.Exit

main :: IO ()
main = do
  args <- getArgs
  case args of
    file:[] -> interpretFile file
    _ -> usage

interpretFile :: FilePath -> IO ()
interpretFile f = readFile f >>= parse' f >>= typecheck' >>= interpret'
  where parse' = handleErr "Syntax error" .* parse
        typecheck' = handleErr "Type error" . typecheck
        interpret' = handleErr "Interpretation error" . interpret

handleErr :: (Show e, Show a) => String -> Either e a -> IO a
handleErr title = either (\err -> do putStrLn title
                                     putStrLn (show err)
                                     exitFailure)
                         (\x -> putStrLn (show x) $> x)

usage :: IO ()
usage = putStrLn "Usage: carth SRC-FILE" >> exitFailure
