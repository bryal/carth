{-# LANGUAGE LambdaCase #-}

module Main where

import Data.Functor
import System.Exit
import System.FilePath
import qualified LLVM.AST

import Misc
import Literate
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
    readFile f >>= parse' f >>= typecheck' >>= monomorphize' >>= interpret'

compileFile :: FilePath -> CompileConfig -> IO ()
compileFile f cfg =
    readFile f
        >>= parse' f
        >>= typecheck'
        >>= monomorphize'
        >>= codegen' f
        >>= compile' cfg

parse' :: FilePath -> String -> IO Ast.Program
parse' f src = do
    src' <- if takeExtension f == ".org"
        then do
            putStrLn "Untangling org..."
            let s = untangleOrg src
            writeFile "out.untangled" s
            pure s
        else pure src
    putStrLn "Parsing..."
    case parse f src' of
        Left e -> putStrLn ("Parse error:\n" ++ show e) >> exitFailure
        Right p -> writeFile "out.parsed" (pretty p) $> p

typecheck' :: Ast.Program -> IO Check.CProgram
typecheck' p = do
    putStrLn "Typechecking..."
    case typecheck p of
        Left e -> putStrLn ("Typecheck error:\n" ++ e) >> exitFailure
        Right p -> writeFile "out.checked" (pretty p) $> p

monomorphize' :: Check.CProgram -> IO Mono.MProgram
monomorphize' p = do
    putStrLn "Monomorphizing..."
    let p' = monomorphize p
    writeFile "out.mono" (pretty p')
    pure p'

codegen' :: FilePath -> Mono.MProgram -> IO LLVM.AST.Module
codegen' f p = do
    putStrLn "Codegen..."
    let m = codegen f p
    writeFile "out.dbgll" (pretty m)
    pure m

interpret' :: Mono.MProgram -> IO ()
interpret' pgm = do
    putStrLn "Interpreting..."
    interpret pgm

compile' :: CompileConfig -> LLVM.AST.Module -> IO ()
compile' cfg mod = do
    putStrLn "Compiling..."
    compile cfg mod
