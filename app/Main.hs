{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Data.Functor
import System.Exit
import System.FilePath
import qualified LLVM.AST

import Misc
import Literate
import qualified TypeErr
import qualified Ast
import qualified AnnotAst
import qualified MonoAst
import Check
import Config
import Interp
import Codegen
import Compile
import Mono
import qualified Parse
import Parse (Source)

main :: IO ()
main = do
    getConfig >>= \case
        ModeInterp infile -> interpretFile infile
        ModeCompile infile cfg -> compileFile infile cfg

interpretFile :: FilePath -> IO ()
interpretFile f = readFile f >>= \src ->
    parse' f src >>= typecheck' f src >>= monomorphize' >>= interpret'

compileFile :: FilePath -> CompileConfig -> IO ()
compileFile f cfg =
    putStrLn ("   Compiling " ++ f ++ "\n") >> readFile f >>= \src ->
        parse' f src
            >>= typecheck' f src
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
    case Parse.parse f src' of
        Left e -> putStrLn (formatParseErr e) >> abort f
        Right p -> writeFile "out.parsed" (pretty p) $> p
  where
    formatParseErr e =
        let ss = lines e in (unlines ((head ss ++ " Error:") : tail ss))

typecheck' :: FilePath -> Source -> Ast.Program -> IO AnnotAst.Program
typecheck' f src p = do
    case typecheck p of
        Left e -> putStrLn (TypeErr.prettyErr e src) >> abort f
        Right p -> writeFile "out.checked" (show p) $> p

monomorphize' :: AnnotAst.Program -> IO MonoAst.Program
monomorphize' p = do
    let p' = monomorphize p
    writeFile "out.mono" (show p')
    pure p'

codegen' :: FilePath -> MonoAst.Program -> IO LLVM.AST.Module
codegen' f p = do
    let m = codegen f p
    writeFile "out.dbgll" (pretty m)
    pure m

interpret' :: MonoAst.Program -> IO ()
interpret' pgm = do
    interpret pgm

compile' :: CompileConfig -> LLVM.AST.Module -> IO ()
compile' cfg mod = do
    compile cfg mod

abort :: FilePath -> IO a
abort f = do
    putStrLn "Error: Aborting due to previous error."
    putStrLn $ "Error: Could not compile/interpret " ++ f ++ "."
    exitFailure
