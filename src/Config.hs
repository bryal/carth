module Config (Config(..)) where

data Config = Config
    { infile :: FilePath
    , outfile :: FilePath
    -- | Path to C compiler to use for linking and compiling ".c" files
    , cc :: FilePath
    , debug :: Bool
    }
