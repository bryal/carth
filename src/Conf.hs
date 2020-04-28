module Conf (Conf(..), CompileConfig(..), RunConfig(..)) where

data Conf
    = CompileConf CompileConfig
    | RunConf RunConfig

data CompileConfig = CompileConfig
    { cInfile :: FilePath
    , cOutfile :: FilePath
    -- | Path to C compiler to use for linking and compiling ".c" files
    , cCompiler :: FilePath
    , cDebug :: Bool }

data RunConfig = RunConfig
    { rInfile :: FilePath
    , rDebug :: Bool }
