{-# LANGUAGE TemplateHaskell #-}

module CompiletimeVars (libDir, modDir) where

import CompiletimeEnv

libDir :: FilePath
libDir = $(lookupCompileEnvOr "CARTH_LIB_DIR" "~/.carth/lib")

modDir :: FilePath
modDir = $(lookupCompileEnvOr "CARTH_MOD_DIR" "~/.carth/mod")
