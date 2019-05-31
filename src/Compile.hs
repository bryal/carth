module Compile (compile) where

import qualified LLVM.AST
import LLVM.Context
import LLVM.Module
import LLVM.Target

-- TODO: Verify w LLVM.Analysis.verify :: Module -> IO ()
-- TODO: CodeGenOpt level
compile :: LLVM.AST.Module -> IO ()
compile mod = withContext $ \c -> withModuleFromAST c mod compileModule

compileModule :: Module -> IO ()
compileModule m = withHostTargetMachine $ \t -> do
    writeLLVMAssemblyToFile (File "out.ll") m
    writeBitcodeToFile (File "out.bc") m
    writeObjectToFile t (File "out.o") m
