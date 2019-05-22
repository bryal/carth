{-# LANGUAGE LambdaCase #-}

module Main where

import qualified Ast
import Check
import Data.Functor
import Interp
import Compile
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
        "-i" : file : [] -> interpretFile file
        file : [] -> compileFile file
        _ -> usage

interpretFile :: FilePath -> IO ()
interpretFile f =
    readFile f >>= parse' f >>= typecheck' >>= monomorphize' >>= interpret'

compileFile :: FilePath -> IO ()
compileFile f =
    readFile f >>= parse' f >>= typecheck' >>= monomorphize' >>= compile' f

parse' :: FilePath -> String -> IO Ast.Program
parse' f src = case parse f src of
    Left e -> putStrLn ("Parse error:\n" ++ show e) >> exitFailure
    Right p -> putStrLn ("Parse result:\n" ++ pretty p ++ "\n") $> p

typecheck' :: Ast.Program -> IO Check.CProgram
typecheck' p = case typecheck p of
    Left e -> putStrLn ("Typecheck error:\n" ++ e) >> exitFailure
    Right p -> putStrLn ("Typecheck result:\n" ++ pretty p ++ "\n") $> p

monomorphize' :: Check.CProgram -> IO Mono.MProgram
monomorphize' p =
    let p' = monomorphize p
    in putStrLn ("Monomorphization result:\n" ++ pretty p' ++ "\n") $> p'

interpret' :: Mono.MProgram -> IO ()
interpret' p = putStrLn "Interpretation result:" >> interpret p

compile' :: FilePath -> Mono.MProgram -> IO ()
compile' f p = putStrLn "Compilation result:" >> compile f p

usage :: IO ()
usage = putStrLn "Usage: carth SRC-FILE" >> exitFailure
