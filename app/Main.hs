{-# LANGUAGE LambdaCase #-}

module Main where

import qualified Annot
import qualified Ast
import Check
import Data.Composition
import Data.Functor
import Interp
import Mono (monomorphize)
import qualified Mono
import Parse
import Pretty
import System.Environment
import System.Exit

main :: IO ()
main = do
    args <- getArgs
    case args of
        file:[] -> interpretFile file
        _ -> usage

interpretFile :: FilePath -> IO ()
interpretFile f =
    readFile f >>= parse' f >>= typecheck' >>= monomorphize' >>= interpret'

parse' :: FilePath -> String -> IO Ast.Program
parse' f src =
    case parse f src of
        Left e -> putStrLn ("Parse error:\n" ++ show e) >> exitFailure
        Right p -> putStrLn ("Parse result:\n" ++ pretty p ++ "\n") $> p

typecheck' :: Ast.Program -> IO Annot.Program
typecheck' p =
    case typecheck p of
        Left e -> putStrLn ("Typecheck error:\n" ++ e) >> exitFailure
        Right p -> putStrLn ("Typecheck result:\n" ++ pretty p ++ "\n") $> p

monomorphize' :: Annot.Program -> IO Mono.Program
monomorphize' p =
    let p' = monomorphize p
    in putStrLn ("Monomorphization result:\n" ++ pretty p' ++ "\n") $> p'

interpret' :: Mono.Program -> IO ()
interpret' p = putStrLn "Interpretation result:" >> interpret p

usage :: IO ()
usage = putStrLn "Usage: carth SRC-FILE" >> exitFailure
