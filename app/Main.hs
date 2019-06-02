{-# LANGUAGE LambdaCase #-}

module Main where

import qualified Ast
import Check
import Data.Functor
import Interp
import Codegen
import Compile
import Mono (monomorphize)
import qualified Mono
import Parse
import Pretty
import System.Environment
import System.Exit
import qualified LLVM.AST

main :: IO ()
main = do
    args <- getArgs
    case args of
        "-i" : file : [] -> interpretFile file
        file : [] -> compileFile file
        _ -> usage

interpretFile :: FilePath -> IO ()
interpretFile f =
    readFile f >>= parse' f >>= typecheck' >>= monomorphize' >>= interpret

compileFile :: FilePath -> IO ()
compileFile f =
    readFile f
        >>= parse' f
        >>= typecheck'
        >>= monomorphize'
        >>= codegen' f
        >>= compile'

parse' :: FilePath -> String -> IO Ast.Program
parse' f src = case parse f src of
    Left e -> putStrLn ("Parse error:\n" ++ show e) >> exitFailure
    Right p -> writeFile "out.parsed" (pretty p) $> p

typecheck' :: Ast.Program -> IO Check.CProgram
typecheck' p = case typecheck p of
    Left e -> putStrLn ("Typecheck error:\n" ++ e) >> exitFailure
    Right p -> writeFile "out.checked" (pretty p) $> p

monomorphize' :: Check.CProgram -> IO Mono.MProgram
monomorphize' p =
    let p' = monomorphize p in writeFile "out.mono" (pretty p') $> p'

codegen' :: FilePath -> Mono.MProgram -> IO LLVM.AST.Module
codegen' f p =
    let m = codegen f p in putStrLn ("Codegen result:\n" ++ pretty m) $> m

compile' :: LLVM.AST.Module -> IO ()
compile' m = putStrLn "Compilation result:" >> compile m

usage :: IO ()
usage = putStrLn "Usage: carth SRC-FILE" >> exitFailure
