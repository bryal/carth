module Conf where

import Control.Monad
import System.FilePath

data Conf
    = CompileConf CompileConfig
    | RunConf RunConfig

data CompileConfig = CompileConfig
    { cInfile :: FilePath
    , cOutfile :: FilePath
    -- | Path to C compiler to use for linking and compiling ".c" files
    , cCompiler :: FilePath
    , cBackend :: Backend
    , cDebug :: Bool
    , cVerbose :: Bool
    , cNoGC :: Bool
    }

data RunConfig = RunConfig
    { rInfile :: FilePath
    , rDebug :: Bool
    , rVerbose :: Bool
    , rNoGC :: Bool
    }

data Backend = BendLLVM | BendC

class Config cfg where
    getDebug :: cfg -> Bool
    getVerbose :: cfg -> Bool
    getNoGC :: cfg -> Bool
instance Config CompileConfig where
    getDebug = cDebug
    getVerbose = cVerbose
    getNoGC = cNoGC
instance Config RunConfig where
    getDebug = rDebug
    getVerbose = rVerbose
    getNoGC = rNoGC

defaultCompileConfig :: FilePath -> CompileConfig
defaultCompileConfig inf = CompileConfig { cInfile = inf
                                         , cOutfile = replaceExtension inf "bin"
                                         , cCompiler = "cc"
                                         , cBackend = BendLLVM
                                         , cDebug = False
                                         , cVerbose = False
                                         , cNoGC = False
                                         }

defaultRunConfig :: FilePath -> RunConfig
defaultRunConfig inf =
    RunConfig { rInfile = inf, rDebug = False, rVerbose = False, rNoGC = False }

verbose :: Config cfg => cfg -> String -> IO ()
verbose cfg msg = when (getVerbose cfg) $ putStrLn msg
