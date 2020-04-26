module Compile (compile) where

import Control.Monad
import LLVM.Context
import LLVM.Module
import LLVM.Target
import LLVM.Analysis
import System.FilePath
import System.Process
import qualified LLVM.Relocation as Reloc
import qualified LLVM.CodeModel as CodeModel
import qualified LLVM.CodeGenOpt as CodeGenOpt

import Config
import qualified Monomorphic
import Codegen


-- TODO: CodeGenOpt level
compile :: FilePath -> Config -> Monomorphic.Program -> IO ()
compile f cfg pgm = withContext $ \c -> withHostTargetMachinePIC $ \t -> do
    layout <- getTargetMachineDataLayout t
    putStrLn ("   Generating LLVM")
    let mod' = codegen layout f pgm
    withModuleFromAST c mod' (compileModule t cfg)

compileModule :: TargetMachine -> Config -> Module -> IO ()
compileModule t cfg m = do
    putStrLn ("   Assembling LLVM")
    let exefile = outfile cfg
        ofile = replaceExtension exefile "o"
    when (debug cfg) $ writeLLVMAssemblyToFile' ".dbg.ll" m
    putStrLn ("   Verifying LLVM")
    verify m
    writeObjectToFile t (File ofile) m
    putStrLn ("   Linking")
    callProcess
        (cc cfg)
        [ "-o"
        , exefile
        , ofile
        , "-l:libcarth_foreign_core.a"
        , "-ldl"
        , "-lpthread"
        ]

-- | `writeLLVMAssemblyToFile` doesn't clear file contents before writing, so
--   this is a workaround.
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
withHostTargetMachinePIC =
    withHostTargetMachine Reloc.PIC CodeModel.Default CodeGenOpt.None
