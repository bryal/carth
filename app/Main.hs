{-# LANGUAGE LambdaCase #-}

module Main where

import Data.Functor
import System.Exit
import qualified LLVM.AST

import Misc
import qualified Ast
import Check
import Config
import Interp
import Codegen
import Compile
import Mono (monomorphize)
import qualified Mono
import Parse

main :: IO ()
main = do
    getConfig >>= \case
        ModeInterp infile -> interpretFile infile
        ModeCompile infile cfg -> compileFile infile cfg

interpretFile :: FilePath -> IO ()
interpretFile f =
    readFile f >>= parse' f >>= typecheck' >>= monomorphize' >>= interpret

compileFile :: FilePath -> CompileConfig -> IO ()
compileFile f cfg =
    readFile f
        >>= parse' f
        >>= typecheck'
        >>= monomorphize'
        >>= codegen' f
        >>= compile cfg

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
codegen' f p = let m = codegen f p in writeFile "out.dbgll" (pretty m) $> m
