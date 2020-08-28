module Conf where

import Control.Monad

data Conf
    = CompileConf CompileConfig
    | RunConf RunConfig

data CompileConfig = CompileConfig
    { cInfile :: FilePath
    , cOutfile :: FilePath
    -- | Path to C compiler to use for linking and compiling ".c" files
    , cCompiler :: FilePath
    , cDebug :: Bool
    , cVerbose :: Bool
    }

data RunConfig = RunConfig
    { rInfile :: FilePath
    , rDebug :: Bool
    , rVerbose :: Bool
    }

class Config cfg where
    getDebug :: cfg -> Bool
    getVerbose :: cfg -> Bool
instance Config CompileConfig where
    getDebug = cDebug
    getVerbose = cVerbose
instance Config RunConfig where
    getDebug = rDebug
    getVerbose = rVerbose

defaultCompileConfig :: FilePath -> FilePath -> CompileConfig
defaultCompileConfig inf outf = CompileConfig { cInfile = inf
                                              , cOutfile = outf
                                              , cCompiler = "cc"
                                              , cDebug = False
                                              , cVerbose = False
                                              }

verbose :: Config cfg => cfg -> String -> IO ()
verbose cfg msg = when (getVerbose cfg) $ putStrLn msg
