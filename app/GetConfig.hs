{-# LANGUAGE TupleSections #-}

-- | Read all the different kinds of configurtion options for Carth. Command
--   line options, config files, environment variables, etc.
module GetConfig (getConfig, Config(..)) where

import System.Console.GetOpt
import System.Environment
import System.Exit
import System.FilePath
import Data.List
import Data.Function
import Control.Monad

import Config


getConfig :: IO Config
getConfig = do
    as <- getArgs
    let subCompile a = a == "c" || a == "compile"
    case as of
        a : as' | subCompile a -> compileCfg as'
        a : _ | a == "-h" || a == "--help" -> do
            putStrLn usageSubs
            exitFailure
        "help" : [] -> do
            putStrLn usageSubs
            exitFailure
        "help" : a : _ | subCompile a -> usageCompile
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

compileCfg :: [String] -> IO Config
compileCfg args = do
    let (fs, extras, errs) = getOpt Permute compileOpts args
    when (not (null errs)) $ putStrLn (concat errs) *> usageCompile
    inf <- case extras of
        f : [] -> pure f
        _ : es -> do
            putStrLn ("Unexpected extra arguments: " ++ intercalate ", " es)
            exitFailure
        [] -> putStrLn "Missing input source file" *> usageCompile
    let outf = dropExtension inf
    when (inf == outf) $ do
        putStrLn
            $ ("Error: Input file \"" ++ inf ++ "\" ")
            ++ "would be overwritten by the generated executable"
        exitFailure
    let defaultCfg =
            Config { infile = inf, outfile = outf, cc = "cc", debug = False }
        cfg = foldl (&) defaultCfg fs
    pure cfg

usageCompile :: IO a
usageCompile = do
    putStrLn $ unlines
        [ "Carth compiler"
        , "Compile a Carth program to an executable"
        , ""
        , usageInfo "Usage: carth c [OPTIONS] SOURCE-FILE" compileOpts
        ]
    exitFailure

compileOpts :: [OptDescr (Config -> Config)]
compileOpts =
    [ Option
        []
        ["cc"]
        (ReqArg (\cc' c -> c { cc = cc' }) "PROGRAM")
        "C compiler to use for linking"
    , Option
        ['o']
        ["outfile"]
        (ReqArg (\f c -> c { outfile = f }) "FILE")
        "Output filepath"
    , Option [] ["debug"] (NoArg (\c -> c { debug = True })) "Enable debugging"
    ]
