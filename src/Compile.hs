{-# LANGUAGE ForeignFunctionInterface, OverloadedStrings, LambdaCase #-}

module Compile (compile, run) where

import LLVM.Context
import LLVM.Module
import LLVM.Target
import LLVM.Analysis
import LLVM.ExecutionEngine
import qualified LLVM.AST as LLAST
import qualified LLVM.Relocation as Reloc
import qualified LLVM.CodeModel as CodeModel
import qualified LLVM.CodeGenOpt as CodeGenOpt
import Control.Monad
import System.FilePath
import System.Process
import System.Exit
import Data.Int
import Data.Functor
import Foreign.Ptr
import Prelude hiding (mod)

import Conf
import qualified Monomorphic
import Codegen


compile :: FilePath -> CompileConfig -> Monomorphic.Program -> IO ()
compile = handleProgram (const compileModule) cDebug

run :: FilePath -> RunConfig -> Monomorphic.Program -> IO ()
run = handleProgram (\ctx _ _ -> mcJitModule ctx) rDebug

-- TODO: CodeGenOpt level
handleProgram
    :: (Context -> TargetMachine -> config -> Module -> IO ())
    -> (config -> Bool)
    -> FilePath
    -> config
    -> Monomorphic.Program
    -> IO ()
handleProgram f debug file cfg pgm = withContext $ \ctx ->
    withHostTargetMachinePIC $ \tm -> do
        layout <- getTargetMachineDataLayout tm
        putStrLn ("   Generating LLVM")
        let amod = codegen layout file pgm
        withModuleFromAST ctx amod $ \mod -> do
            putStrLn ("   Assembling LLVM")
            when (debug cfg) $ writeLLVMAssemblyToFile' ".dbg.ll" mod
            putStrLn ("   Verifying LLVM")
            verify mod
            f ctx tm cfg mod

compileModule :: TargetMachine -> CompileConfig -> Module -> IO ()
compileModule tm cfg mod = do
    let exefile = cOutfile cfg
        ofile = replaceExtension exefile "o"
    writeObjectToFile tm (File ofile) mod
    putStrLn ("   Linking")
    callProcess
        (cCompiler cfg)
        [ "-o"
        , exefile
        , ofile
        , "-l:libcarth_foreign_core.a"
        , "-ldl"
        , "-lpthread"
        ]

foreign import ccall "dynamic"
  mkMain :: FunPtr (IO Int32) -> IO Int32

mcJitModule :: Context -> Module -> IO ()
mcJitModule ctx mod = do
    putStrLn "   Running with MCJIT"
    withMCJIT ctx Nothing Nothing Nothing Nothing $ \engine ->
        withModuleInEngine engine mod $ \execMod ->
            getFunction execMod (LLAST.Name "main") >>= \case
                Just mainAddr -> mkMain (castFunPtr mainAddr) $> ()
                Nothing -> putStrLn "Error getting main" >> exitFailure

-- | `writeLLVMAssemblyToFile` doesn't clear file contents before writing,
--   so this is a workaround.
writeLLVMAssemblyToFile' :: FilePath -> Module -> IO ()
writeLLVMAssemblyToFile' f m = do
    writeFile f ""
    writeLLVMAssemblyToFile (File f) m

withHostTargetMachinePIC :: (TargetMachine -> IO a) -> IO a
withHostTargetMachinePIC =
    withHostTargetMachine Reloc.PIC CodeModel.Default CodeGenOpt.None
