{-# LANGUAGE TupleSections #-}

-- | Read all the different kinds of configurtion options for Carth. Command
--    line options, config files, environment variables, etc.
module Config (getConfig, ModeConfig(..)) where

import Compile
import System.Console.GetOpt
import System.Environment
import System.Exit
import Data.List
import Data.Function
import Control.Monad

data ModeConfig
    = ModeInterp FilePath
    | ModeCompile FilePath CompileConfig

getConfig :: IO ModeConfig
getConfig = do
    as <- getArgs
    case as of
        a : as' | a == "i" || a == "interpret" -> interpCfg as'
        a : as' | a == "c" || a == "compile" -> compileCfg as'
        a : _ | a == "-h" || a == "--help" -> do
            putStrLn usageSubs
            exitFailure
        "help" : [] -> do
            putStrLn usageSubs
            exitFailure
        "help" : a : _ | a == "i" || a == "interpret" -> usageInterp
        "help" : a : _ | a == "c" || a == "compile" -> usageCompile
        a : _ -> do
            putStrLn ("Error: `" ++ a ++ "` is not a valid subcommand\n")
            putStrLn usageSubs
            exitFailure
        [] -> do
            putStrLn "Error: No subcommand given\n"
            putStrLn usageSubs
            exitFailure

usageSubs :: String
usageSubs = unlines
    [ "Usage: carth SUBCOMMAND ..."
    , ""
    , "Available subcommands are:"
    , "  i, interpret     Interpret a source file"
    , "  c, compile       Compile a source file"
    , ""
    , "See `carth help SUBCOMMAND` for help on a specific subcommand"
    ]

interpCfg :: [String] -> IO ModeConfig
interpCfg args = do
    let (_, extras, errs) = getOpt Permute interpOpts args
    when (not (null errs)) $ putStrLn (concat errs) *> usageInterp
    case extras of
        infile : [] -> pure (ModeInterp infile)
        _ : es -> do
            putStrLn ("Unexpected extra arguments: " ++ intercalate ", " es)
            exitFailure
        [] -> putStrLn "Missing input source file" *> usageInterp

compileCfg :: [String] -> IO ModeConfig
compileCfg args = do
    let (fs, extras, errs) = getOpt Permute compileOpts args
    when (not (null errs)) $ putStrLn (concat errs) *> usageCompile
    let cfg = foldl (&) defaultCompileConfig fs
    case extras of
        infile : [] -> pure (ModeCompile infile cfg)
        _ : es -> do
            putStrLn ("Unexpected extra arguments: " ++ intercalate ", " es)
            exitFailure
        [] -> putStrLn "Missing input source file" *> usageCompile

usageInterp :: IO a
usageInterp = do
    putStrLn $ unlines
        [ "Carth interpreter"
        , "Run a Carth program by interpreting a source file"
        , ""
        , usageInfo "Usage: carth i [OPTIONS] SOURCE-FILE" interpOpts
        ]
    exitFailure

usageCompile :: IO a
usageCompile = do
    putStrLn $ unlines
        [ "Carth compiler"
        , "Compile a Carth program to an executable"
        , ""
        , usageInfo "Usage: carth c [OPTIONS] SOURCE-FILE" compileOpts
        ]
    exitFailure

-- getOpt :: ArgOrder a -> [OptDescr a] -> [String] -> ([a], [String], [String])

interpOpts :: [OptDescr ()]
interpOpts = []

compileOpts :: [OptDescr (CompileConfig -> CompileConfig)]
compileOpts =
    [ Option
        []
        ["cc"]
        (ReqArg (\cc' cfg -> cfg { cc = cc' }) "PROGRAM")
        "C compiler to use for linking and compiling C files"
    , Option
        ['o']
        ["outfile"]
        (ReqArg (\f cfg -> cfg { outfile = Just f }) "FILE")
        "Output filepath"
    ]
