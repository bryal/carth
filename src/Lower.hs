module Lower (lower) where

import qualified Monomorphic
import Low

lower :: Monomorphic.Program -> Program
lower = id
