{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Data.Functor
import System.Exit
import System.FilePath

import Misc
import Literate
import qualified TypeErr
import qualified Ast
import qualified DesugaredAst
import qualified MonoAst
import Check
import Config
import Compile
import Mono
import qualified Parse
import Parse (Source)

main :: IO ()
main = uncurry compileFile =<< getConfig

compileFile :: FilePath -> CompileConfig -> IO ()
compileFile f cfg = do
    putStrLn ("   Compiling " ++ f ++ "\n")
    src <- readFile f
    parse' f src >>= typecheck' f src >>= monomorphize' >>= compile f cfg

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

typecheck' :: FilePath -> Source -> Ast.Program -> IO DesugaredAst.Program
typecheck' f src p = case typecheck p of
    Left e -> putStrLn (TypeErr.prettyErr e src) >> abort f
    Right p -> writeFile "out.checked" (show p) $> p

monomorphize' :: DesugaredAst.Program -> IO MonoAst.Program
monomorphize' p = do
    let p' = monomorphize p
    writeFile "out.mono" (show p')
    pure p'

abort :: FilePath -> IO a
abort f = do
    putStrLn "Error: Aborting due to previous error."
    putStrLn $ "Error: Could not compile " ++ f ++ "."
    exitFailure
