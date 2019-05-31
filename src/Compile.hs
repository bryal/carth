module Compile (compile) where

import qualified LLVM.AST
import LLVM.Context
import LLVM.Module
import LLVM.Target
import Data.Function.Slip

-- TODO: Verify w LLVM.Analysis.verify :: Module -> IO ()
-- TODO: CodeGenOpt level
compile :: LLVM.AST.Module -> IO ()
compile mod = withContext $ (slipr withModuleFromAST)
    mod
    (withHostTargetMachine . slipr writeObjectToFile (File "out.o"))
