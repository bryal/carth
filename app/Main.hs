{-# LANGUAGE LambdaCase, BangPatterns #-}

module Main (main) where

import System.Environment
import Control.Monad
import Control.Monad.Except
import Prelude hiding (lex)

import Misc
import Pretty
import qualified Front.Err as Err
import qualified Front.Lexd as Lexd
import qualified Front.Parsed as Parsed
import qualified Front.Checked as Checked
import Front.Check
import Conf
import GetConfig
import Back.CompileLLVM as CompileLLVM
import Back.CompileC as CompileC
import Back.Link as Link
import Front.Monomorphize
import Back.Lower
import qualified Back.Low as Ast
import qualified Front.Parse as Parse
import qualified Front.Lex as Lex
import qualified Front.Macro as Macro
import EnvVars

main :: IO ()
main = getConfig >>= \case
    CompileConf cfg -> compileFile cfg
    RunConf cfg -> runFile cfg

compileFile :: CompileConfig -> IO ()
compileFile cfg = do
    let f = cInfile cfg
    putStrLn ("   Compiling " ++ f ++ "")
    verbose cfg "     Environment variables:"
    lp <- lookupEnv "LIBRARY_PATH"
    mp <- modulePaths
    verbose cfg ("       library path = " ++ show lp)
    verbose cfg ("       module paths = " ++ show mp)
    !low <- frontend cfg f
    case cBackend cfg of
        BendLLVM -> CompileLLVM.compile f cfg low
        BendC -> CompileC.compile cfg low
    Link.link cfg
    putStrLn ""

runFile :: RunConfig -> IO ()
runFile cfg = do
    let f = rInfile cfg
    putStrLn ("   Running " ++ f ++ "")
    verbose cfg "     Environment variables:"
    mp <- modulePaths
    verbose cfg ("       module paths = " ++ show mp)
    !mon <- frontend cfg f
    CompileLLVM.run f cfg mon
    putStrLn ""

frontend :: Config cfg => cfg -> FilePath -> IO Ast.Program
frontend cfg f = do
    let d = getDebug cfg
    verbose cfg "   Lexing"
    !tts <- lex f
    when d $ writeFile ".dbg.lexd" (show tts)
    verbose cfg "   Expanding macros"
    !tts' <- expandMacros f tts
    when d $ writeFile ".dbg.expanded" (show tts')
    verbose cfg "   Parsing"
    !ast <- parse f tts'
    verbose cfg "   Typechecking"
    !ann <- typecheck' f ast
    when d $ writeFile ".dbg.checked" (show ann)
    verbose cfg "   Monomorphizing"
    let !mon = monomorphize ann
    when d $ writeFile ".dbg.mono" (show mon)
    verbose cfg "   Lowering"
    let !low = lower (getNoGC cfg) mon
    when d $ writeFile ".dbg.low" (pretty low)
    pure low

lex :: FilePath -> IO [Lexd.TokenTree]
lex f = runExceptT (Lex.lex f) >>= \case
    Left e -> putStrLn (formatLexErr e) >> abort f
    Right p -> pure p
    where formatLexErr e = let ss = lines e in unlines ((head ss ++ " Error:") : tail ss)

expandMacros :: FilePath -> [Lexd.TokenTree] -> IO [Lexd.TokenTree]
expandMacros f tts = case runExcept (Macro.expandMacros tts) of
    Left e -> Err.printMacroErr e >> abort f
    Right p -> pure p

parse :: FilePath -> [Lexd.TokenTree] -> IO Parsed.Program
parse f tts = do
    let (result, messages) = Parse.parse tts
    forM_ messages $ \case
        Parsed.Warning pos msg -> Err.posd' "warning" pos msg
    case result of
        Left e -> Err.printParseErr e >> abort f
        Right p -> pure p

typecheck' :: FilePath -> Parsed.Program -> IO Checked.Program
typecheck' f p = case typecheck p of
    Left e -> Err.printTypeErr e >> abort f
    Right p -> pure p
