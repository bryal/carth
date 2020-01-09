{-# LANGUAGE TupleSections #-}

-- | Read all the different kinds of configurtion options for Carth. Command
--    line options, config files, environment variables, etc.
module Config (getConfig, ModeConfig) where

import System.Console.GetOpt
import System.Environment
import System.Exit
import Data.List
import Data.Function
import Control.Monad

import Compile


type ModeConfig = (FilePath, CompileConfig)

getConfig :: IO ModeConfig
getConfig = do
    as <- getArgs
    case as of
        a : as' | a == "c" || a == "compile" -> compileCfg as'
        a : _ | a == "-h" || a == "--help" -> do
            putStrLn usageSubs
            exitFailure
        "help" : [] -> do
            putStrLn usageSubs
            exitFailure
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
    , "  c, compile       Compile a source file"
    , ""
    , "See `carth help SUBCOMMAND` for help on a specific subcommand"
    ]

compileCfg :: [String] -> IO ModeConfig
compileCfg args = do
    let (fs, extras, errs) = getOpt Permute compileOpts args
    when (not (null errs)) $ putStrLn (concat errs) *> usageCompile
    let cfg = foldl (&) defaultCompileConfig fs
    case extras of
        infile : [] -> pure (infile, cfg)
        _ : es -> do
            putStrLn ("Unexpected extra arguments: " ++ intercalate ", " es)
            exitFailure
        [] -> putStrLn "Missing input source file" *> usageCompile

usageCompile :: IO a
usageCompile = do
    putStrLn $ unlines
        [ "Carth compiler"
        , "Compile a Carth program to an executable"
        , ""
        , usageInfo "Usage: carth c [OPTIONS] SOURCE-FILE" compileOpts
        ]
    exitFailure

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
