module Compile (compile, CompileConfig(..), defaultCompileConfig) where

import qualified LLVM.AST
import LLVM.Context
import LLVM.Module
import LLVM.Target
import Data.Maybe
import System.FilePath
import System.Process
import qualified LLVM.Relocation as Reloc
import qualified LLVM.CodeModel as CodeModel
import qualified LLVM.CodeGenOpt as CodeGenOpt

-- | Configuration for LLVM compilation and CC linking
data CompileConfig = CompileConfig
    -- | Path to C compiler to use for linking and compiling ".c" files
    { cc :: FilePath
    -- | Filepath to write the output item to. If none is supplied, a default
    --   name of "out" with the appropriate extension will be used.
    , outfile :: Maybe FilePath }

defaultCompileConfig :: CompileConfig
defaultCompileConfig = CompileConfig { cc = "cc", outfile = Nothing }

-- TODO: Verify w LLVM.Analysis.verify :: Module -> IO ()
-- TODO: CodeGenOpt level
compile :: CompileConfig -> LLVM.AST.Module -> IO ()
compile cfg mod =
    withContext $ \c -> withModuleFromAST c mod (compileModule cfg)

compileModule :: CompileConfig -> Module -> IO ()
compileModule cfg m = withHostTargetMachinePIC $ \t -> do
    let binfile = fromMaybe "out" (outfile cfg)
        llfile = replaceExtension binfile "ll"
        bcfile = replaceExtension binfile "bc"
        ofile = replaceExtension binfile "o"
    writeLLVMAssemblyToFile (File llfile) m
    writeBitcodeToFile (File bcfile) m
    writeObjectToFile t (File ofile) m
    callProcess (cc cfg) ["-o", binfile, ofile, "lib/lib.c"]

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
