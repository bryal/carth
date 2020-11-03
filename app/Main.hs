{-# LANGUAGE LambdaCase #-}

module Main (main) where

import System.Environment
import Control.Monad
import Control.Monad.Except
import Prelude hiding (lex)

import Misc
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
import qualified Macro
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
    tts <- lex f
    when d $ writeFile ".dbg.lexd" (show tts)
    verbose cfg ("   Expanding macros")
    tts' <- expandMacros f tts
    when d $ writeFile ".dbg.expanded" (show tts')
    verbose cfg ("   Parsing")
    ast <- parse f tts'
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
lex f = runExceptT (Lex.lex f) >>= \case
    Left e -> putStrLn (formatLexErr e) >> abort f
    Right p -> pure p
  where
    formatLexErr e = let ss = lines e in (unlines ((head ss ++ " Error:") : tail ss))

expandMacros :: FilePath -> [Lexd.TokenTree] -> IO [Lexd.TokenTree]
expandMacros f tts = case runExcept (Macro.expandMacros tts) of
    Left e -> Err.printMacroErr e >> abort f
    Right p -> pure p

parse :: FilePath -> [Lexd.TokenTree] -> IO Parsed.Program
parse f tts = case runExcept (Parse.parse tts) of
    Left e -> Err.printParseErr e >> abort f
    Right p -> pure p

typecheck' :: FilePath -> Parsed.Program -> IO Checked.Program
typecheck' f p = case typecheck p of
    Left e -> Err.printTypeErr e >> abort f
    Right p -> pure p
