module EnvVars (modulePaths) where

import System.Environment (lookupEnv)

import Misc


modulePaths :: IO [FilePath]
modulePaths = fmap (maybe [] (splitOn ":")) (lookupEnv "CARTH_MODULE_PATH")
