{-# LANGUAGE LambdaCase #-}

module Main (main) where

import System.Environment
import Control.Monad

import Misc
import Pretty
import qualified TypeErr
import qualified Ast
import qualified DesugaredAst
import Check
import GetConfig
import Compile
import Mono
import qualified Parse
import EnvVars

main :: IO ()
main = compileFile =<< getConfig

compileFile :: Config -> IO ()
compileFile cfg = do
    let (d, f) = (debug cfg, infile cfg)
    putStrLn ("   Compiling " ++ f ++ "")
    putStrLn ("     Environment variables:")
    lp <- lookupEnv "LIBRARY_PATH"
    mp <- modulePaths
    putStrLn ("       library path = " ++ show lp)
    putStrLn ("       module paths = " ++ show mp)
    putStrLn ("   Parsing")
    ast <- parse f
    when d $ writeFile ".dbg.parsed" (pretty ast)
    putStrLn ("   Typechecking")
    ann <- typecheck' f ast
    when d $ writeFile ".dbg.checked" (show ann)
    putStrLn ("   Monomorphizing")
    let mon = monomorphize ann
    when d $ writeFile ".dbg.mono" (show mon)
    compile f cfg mon
    putStrLn ""

parse :: FilePath -> IO Ast.Program
parse f = Parse.parse f >>= \case
    Left e -> putStrLn (formatParseErr e) >> abort f
    Right p -> pure p
  where
    formatParseErr e =
        let ss = lines e in (unlines ((head ss ++ " Error:") : tail ss))

typecheck' :: FilePath -> Ast.Program -> IO DesugaredAst.Program
typecheck' f p = case typecheck p of
    Left e -> TypeErr.printErr e >> abort f
    Right p -> pure p
