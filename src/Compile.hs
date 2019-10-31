module Compile (compile, CompileConfig(..), defaultCompileConfig) where

import LLVM.Context
import LLVM.Module
import LLVM.Target
import Data.Maybe
import System.FilePath
import System.Process
import qualified LLVM.Relocation as Reloc
import qualified LLVM.CodeModel as CodeModel
import qualified LLVM.CodeGenOpt as CodeGenOpt
import LLVM.Internal.EncodeAST (runEncodeAST)

import Misc
import qualified MonoAst
import Codegen

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
compile :: FilePath -> CompileConfig -> MonoAst.Program -> IO ()
compile f cfg pgm = withContext $ \c -> do
    mod <- runEncodeAST c $ codegen f pgm
    writeFile "out.dbgll" (pretty mod)
    withModuleFromAST c mod (compileModule cfg)

compileModule :: CompileConfig -> Module -> IO ()
compileModule cfg m = withHostTargetMachinePIC $ \t -> do
    let binfile = fromMaybe "out" (outfile cfg)
        llfile = replaceExtension binfile "ll"
        bcfile = replaceExtension binfile "bc"
        ofile = replaceExtension binfile "o"
    writeLLVMAssemblyToFile' llfile m
    writeBitcodeToFile (File bcfile) m
    writeObjectToFile t (File ofile) m
    callProcess
        (cc cfg)
        [ "-o"
        , binfile
        , ofile
        , "/home/jojo/Hack/carth/foreign-core/target/debug/libcarth_foreign_core.a"
        , "-ldl"
        , "-lpthread"
        ]

-- | `writeLLVMAssemblyToFile` doesn't clear file contents before writing, so this
--   is a workaround.
--
--   If the file was previously 100 lines of data, and the new LLVM-assembly is
--   70 lines, the first 70 lines will be overwritten, but the remaining 30 will
--   be the same as in the old file, which will cause errors if we try to
--   compile it manually. So we have to clear file contents first manually if we
--   want these dumps to be useful for debugging.
writeLLVMAssemblyToFile' :: FilePath -> Module -> IO ()
writeLLVMAssemblyToFile' f m = do
    writeFile f ""
    writeLLVMAssemblyToFile (File f) m

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
