module Optimize (optimize) where

import qualified Monomorphic
import Optimized

optimize :: Monomorphic.Program -> Program
optimize = id
