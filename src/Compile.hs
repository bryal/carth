module Compile (compile) where

import qualified LLVM.AST
import LLVM.Context
import LLVM.Module
import LLVM.Target
import qualified LLVM.Relocation as Reloc
import qualified LLVM.CodeModel as CodeModel
import qualified LLVM.CodeGenOpt as CodeGenOpt

-- TODO: Verify w LLVM.Analysis.verify :: Module -> IO ()
-- TODO: CodeGenOpt level
compile :: LLVM.AST.Module -> IO ()
compile mod = withContext $ \c -> withModuleFromAST c mod compileModule

compileModule :: Module -> IO ()
    writeLLVMAssemblyToFile (File "out.ll") m
    writeBitcodeToFile (File "out.bc") m
    writeObjectToFile t (File "out.o") m
compileModule m = withHostTargetMachinePIC $ \t -> do

withHostTargetMachinePIC :: (TargetMachine -> IO a) -> IO a
withHostTargetMachinePIC f = do
    initializeAllTargets
    trip <- getDefaultTargetTriple
    (targ, _) <- lookupTarget Nothing trip
    cpu <- getHostCPUName
    features <- getHostCPUFeatures
    withTargetOptions $ \opts -> withTargetMachine
        targ
        trip
        cpu
        features
        opts
        Reloc.PIC
        CodeModel.Default
        CodeGenOpt.Aggressive
        f
