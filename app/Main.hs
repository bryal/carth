{-# LANGUAGE LambdaCase #-}

module Main (main) where

import System.Environment
import Control.Monad

import Misc
import Pretty
import qualified TypeErr
import qualified Parsed
import qualified Checked
import Check
import Conf
import GetConfig
import Compile
import Monomorphize
import qualified Monomorphic
import qualified Parse
import EnvVars

main :: IO ()
main = getConfig >>= \case
    CompileConf cfg -> compileFile cfg
    RunConf cfg -> runFile cfg

compileFile :: CompileConfig -> IO ()
compileFile cfg = do
    let f = cInfile cfg
    putStrLn ("   Compiling " ++ f ++ "")
    putStrLn ("     Environment variables:")
    lp <- lookupEnv "LIBRARY_PATH"
    mp <- modulePaths
    putStrLn ("       library path = " ++ show lp)
    putStrLn ("       module paths = " ++ show mp)
    mon <- frontend (cDebug cfg) f
    compile f cfg mon
    putStrLn ""

runFile :: RunConfig -> IO ()
runFile cfg = do
    let f = rInfile cfg
    putStrLn ("   Running " ++ f ++ "")
    putStrLn ("     Environment variables:")
    mp <- modulePaths
    putStrLn ("       module paths = " ++ show mp)
    mon <- frontend (rDebug cfg) f
    run f cfg mon
    putStrLn ""

frontend :: Bool -> FilePath -> IO Monomorphic.Program
frontend d f = do
    putStrLn ("   Parsing")
    ast <- parse f
    when d $ writeFile ".dbg.parsed" (pretty ast)
    putStrLn ("   Typechecking")
    ann <- typecheck' f ast
    when d $ writeFile ".dbg.checked" (show ann)
    putStrLn ("   Monomorphizing")
    let mon = monomorphize ann
    when d $ writeFile ".dbg.mono" (show mon)
    pure mon

parse :: FilePath -> IO Parsed.Program
parse f = Parse.parse f >>= \case
    Left e -> putStrLn (formatParseErr e) >> abort f
    Right p -> pure p
  where
    formatParseErr e =
        let ss = lines e in (unlines ((head ss ++ " Error:") : tail ss))

typecheck' :: FilePath -> Parsed.Program -> IO Checked.Program
typecheck' f p = case typecheck p of
    Left e -> TypeErr.printErr e >> abort f
    Right p -> pure p
