{-# LANGUAGE TupleSections, TemplateHaskell, RankNTypes #-}

-- | Read all the different kinds of configurtion options for Carth. Command
--   line options, config files, environment variables, etc.
module GetConfig (getConfig, Conf(..)) where

import System.Console.GetOpt
import System.Environment
import System.Exit
import System.FilePath
import Data.List
import Data.Function
import Control.Monad

import Conf
import Prebaked


getConfig :: IO Conf
getConfig = do
    as <- getArgs
    let subCompile a = a == "c" || a == "compile"
    let subRun a = a == "r" || a == "run"
    case as of
        a : as'
            | subCompile a -> compileCfg as'
            | subRun a -> runCfg as'
        a : _ | a == "-h" || a == "--help" -> do
            putStrLn usageSubs
            exitFailure
        "help" : [] -> do
            putStrLn usageSubs
            exitFailure
        "help" : a : _
            | subCompile a -> usageCompile
            | subRun a -> usageRun
        "version" : _ -> printVersion >> exitSuccess
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
    , "  r, run           JIT run a source file"
    , "     version       Show version information"
    , ""
    , "See `carth help SUBCOMMAND` for help on a specific subcommand"
    ]

compileCfg :: [String] -> IO Conf
compileCfg args = do
    (fs, inf) <- get args compileOpts usageCompile
    let outf = dropExtension inf
    when (inf == outf) $ do
        putStrLn
            $ ("Error: Input file \"" ++ inf ++ "\" ")
            ++ "would be overwritten by the generated executable"
        exitFailure
    let defaultCfg = CompileConfig
            { cInfile = inf
            , cOutfile = outf
            , cCompiler = "cc"
            , cDebug = False
            , cVerbose = False
            }
        cfg = foldl (&) defaultCfg fs
    pure (CompileConf cfg)

runCfg :: [String] -> IO Conf
runCfg args = do
    (fs, inf) <- get args runOpts usageRun
    let defaultCfg = RunConfig { rInfile = inf, rDebug = False, rVerbose = False }
        cfg = foldl (&) defaultCfg fs
    pure (RunConf cfg)

get
    :: [String]
    -> [OptDescr (cfg -> cfg)]
    -> (forall a . IO a)
    -> IO ([cfg -> cfg], FilePath)
get args opts usage = do
    let (fs, extras, errs) = getOpt Permute opts args
    when (not (null errs)) $ putStrLn (concat errs) *> usage
    inf <- case extras of
        f : [] -> pure f
        _ : es -> do
            putStrLn ("Unexpected extra arguments: " ++ intercalate ", " es)
            usage
        [] -> putStrLn "Missing input source file" *> usage
    pure (fs, inf)

usageCompile :: IO a
usageCompile = do
    putStrLn $ unlines
        [ "Carth compile"
        , "Compile a Carth program to an executable"
        , ""
        , usageInfo "Usage: carth c [OPTIONS] SOURCE-FILE" compileOpts
        ]
    exitFailure

usageRun :: IO a
usageRun = do
    putStrLn $ unlines
        [ "Carth run"
        , "JIT run Carth program"
        , ""
        , usageInfo "Usage: carth r [OPTIONS] SOURCE-FILE" runOpts
        ]
    exitFailure

compileOpts :: [OptDescr (CompileConfig -> CompileConfig)]
compileOpts =
    [ Option
        []
        ["cc"]
        (ReqArg (\cc' c -> c { cCompiler = cc' }) "PROGRAM")
        "C compiler to use for linking"
    , Option
        ['o']
        ["outfile"]
        (ReqArg (\f c -> c { cOutfile = f }) "FILE")
        "Output filepath"
    , Option [] ["debug"] (NoArg (\c -> c { cDebug = True })) "Enable debugging"
    , Option ['v'] ["verbose"] (NoArg (\c -> c { cVerbose = True })) "Verbose output"
    ]

runOpts :: [OptDescr (RunConfig -> RunConfig)]
runOpts =
    [ Option [] ["debug"] (NoArg (\c -> c { rDebug = True })) "Enable debugging"
    , Option ['v'] ["verbose"] (NoArg (\c -> c { rVerbose = True })) "Verbose output"
    ]

printVersion :: IO ()
printVersion = do
    let (major, minor, patch) = version
    let versionStr = concat [show major, ".", show minor, ".", show patch]
    putStrLn ("Carth " ++ versionStr)

version :: (Int, Int, Int)
version = $(readCompilerVersion)
