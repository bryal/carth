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
    , cLinker :: FilePath
    , cBackend :: Backend
    , cDebug :: Bool
    , cVerbose :: Bool
    }

data RunConfig = RunConfig
    { rInfile :: FilePath
    , rDebug :: Bool
    , rVerbose :: Bool
    }

data Backend = BendLLVM | BendC

class Config cfg where
    getDebug :: cfg -> Bool
    getVerbose :: cfg -> Bool
instance Config CompileConfig where
    getDebug = cDebug
    getVerbose = cVerbose
instance Config RunConfig where
    getDebug = rDebug
    getVerbose = rVerbose

defaultCompileConfig :: FilePath -> CompileConfig
defaultCompileConfig inf = CompileConfig { cInfile = inf
                                         , cOutfile = replaceExtension inf "bin"
                                         , cCompiler = "cc"
                                         , cLinker = "mold"
                                         , cBackend = BendC
                                         , cDebug = False
                                         , cVerbose = False
                                         }

defaultRunConfig :: FilePath -> RunConfig
defaultRunConfig inf = RunConfig { rInfile = inf, rDebug = False, rVerbose = False }

verbose :: Config cfg => cfg -> String -> IO ()
verbose cfg msg = when (getVerbose cfg) $ putStrLn msg
