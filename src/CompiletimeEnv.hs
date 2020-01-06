module CompiletimeEnv (lookupCompileEnvOr) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Lift(..))
import System.Environment (lookupEnv)
import Data.Maybe

-- | Looks up a compile-time environment variable.
lookupCompileEnvOr :: String -> String -> Q Exp
lookupCompileEnvOr key def = (lift . fromMaybe def) =<< lookupCompileEnvOr' key

lookupCompileEnvOr' :: String -> Q (Maybe String)
lookupCompileEnvOr' key = runIO (lookupEnv key)
