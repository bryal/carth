{-# LANGUAGE LambdaCase #-}

module Main where

import Pretty
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
interpretFile f = readFile f >>= parse' f >>= typecheck' >>= interpret'
  where
    parse' = handleErr "Parse" show pretty .* parse
    typecheck' = handleErr "Typecheck" id pretty . typecheck
    interpret' = handleErr "Interpret" id show . interpret

handleErr :: String -> (e -> String) -> (a -> String) -> Either e a -> IO a
handleErr title f g = either (\e -> do putStrLn (title ++ " error:")
                                       putStrLn (f e)
                                       exitFailure)
                             (\x -> do putStrLn (title ++ " result:")
                                       putStrLn (g x ++ "\n")
                                       pure x)

usage :: IO ()
usage = putStrLn "Usage: carth SRC-FILE" >> exitFailure
