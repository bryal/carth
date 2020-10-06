{-# LANGUAGE LambdaCase #-}

module Main (main) where

import System.Environment
import Control.Monad
import Prelude hiding (lex)

import Misc
import Pretty
import qualified Err
import qualified Lexd
import qualified Parsed
import qualified Checked
import Check
import Conf
import GetConfig
import Compile
import Monomorphize
import Optimize
import qualified Optimized as Ast
import qualified Parse
import qualified Lex
import EnvVars

main :: IO ()
main = getConfig >>= \case
    CompileConf cfg -> compileFile cfg
    RunConf cfg -> runFile cfg

compileFile :: CompileConfig -> IO ()
compileFile cfg = do
    let f = cInfile cfg
    putStrLn ("   Compiling " ++ f ++ "")
    verbose cfg ("     Environment variables:")
    lp <- lookupEnv "LIBRARY_PATH"
    mp <- modulePaths
    verbose cfg ("       library path = " ++ show lp)
    verbose cfg ("       module paths = " ++ show mp)
    mon <- frontend cfg f
    compile f cfg mon
    putStrLn ""

runFile :: RunConfig -> IO ()
runFile cfg = do
    let f = rInfile cfg
    putStrLn ("   Running " ++ f ++ "")
    verbose cfg ("     Environment variables:")
    mp <- modulePaths
    verbose cfg ("       module paths = " ++ show mp)
    mon <- frontend cfg f
    run f cfg mon
    putStrLn ""

frontend :: Config cfg => cfg -> FilePath -> IO Ast.Program
frontend cfg f = do
    let d = getDebug cfg
    verbose cfg ("   Lexing")
    cst <- lex f
    when d $ writeFile ".dbg.lexd" (show cst)
    verbose cfg ("   Parsing")
    ast <- parse f
    when d $ writeFile ".dbg.parsed" (pretty ast)
    verbose cfg ("   Typechecking")
    ann <- typecheck' f ast
    when d $ writeFile ".dbg.checked" (show ann)
    verbose cfg ("   Monomorphizing")
    let mon = monomorphize ann
    when d $ writeFile ".dbg.mono" (show mon)
    let opt = optimize mon
    when d $ writeFile ".dbg.opt" (show opt)
    pure opt

lex :: FilePath -> IO [Lexd.TokenTree]
lex f = Lex.lex f >>= \case
    Left e -> putStrLn (formatParseErr e) >> abort f
    Right p -> pure p
  where
    formatParseErr e = let ss = lines e in (unlines ((head ss ++ " Error:") : tail ss))

parse :: FilePath -> IO Parsed.Program
parse f = Parse.parse f >>= \case
    Left e -> putStrLn (formatParseErr e) >> abort f
    Right p -> pure p
  where
    formatParseErr e = let ss = lines e in (unlines ((head ss ++ " Error:") : tail ss))

typecheck' :: FilePath -> Parsed.Program -> IO Checked.Program
typecheck' f p = case typecheck p of
    Left e -> Err.printTypeErr e >> abort f
    Right p -> pure p
