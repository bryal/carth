{-# LANGUAGE LambdaCase #-}

module Main where

import Data.Functor
import Lib

import System.Environment
import System.Exit

main :: IO ()
main = do
  args <- getArgs
  case args of
    file:[] -> interpretFile file
    _ -> usage

interpretFile :: FilePath -> IO ()
interpretFile file = parseFile file <&> interpret >>= \case
  Left err -> do
    putStrLn "Interpretation error"
    putStrLn err
    exitFailure
  Right () -> pure ()

parseFile :: String -> IO Program
parseFile file = readFile file <&> parse file >>= \case
  Left err -> do
    putStrLn "Syntax error"
    print err
    exitFailure
  Right pgm -> print pgm >> pure pgm

usage :: IO ()
usage = putStrLn "Usage: carth SRC-FILE" >> exitFailure
