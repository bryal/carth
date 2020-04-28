{-# LANGUAGE ForeignFunctionInterface, OverloadedStrings, LambdaCase #-}

module Compile (compile, run, runOrc) where

import LLVM.Context
import LLVM.Module
import LLVM.Target
import LLVM.Analysis
import LLVM.OrcJIT
import LLVM.OrcJIT.CompileLayer
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
import Data.IORef
import qualified Data.Map as Map
import Foreign.Ptr
import Prelude hiding (mod)

import Conf
import qualified Monomorphic
import Codegen


compile :: FilePath -> CompileConfig -> Monomorphic.Program -> IO ()
compile = handleProgram (const compileModule) cDebug

run :: FilePath -> RunConfig -> Monomorphic.Program -> IO ()
run = handleProgram (\ctx _ _ -> mcJitModule ctx) rDebug

runOrc :: FilePath -> RunConfig -> Monomorphic.Program -> IO ()
runOrc = handleProgram (\_ tm _ -> orcJitModule tm) rDebug

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

-- FIXME: Works if there are no external symbols declared, i.e. if it's a
--        carth-only program, so to speak. As soon as we need symbols from
--        carth_foreign_core or so, it breaks down.
--
--        If we load libcarth_foreign_core.{so/a} with extra-libraries in
--        package.yaml, there's no difference. If we load the .so with
--        loadLibraryPermanently, getSymbolAddressInProcess can find
--        e.g. add-int, but symbol resolution still fails at some point, and the
--        last printed line from `resolver` says `add-int`, so idk what's going
--        on.
orcJitModule :: TargetMachine -> Module -> IO ()
orcJitModule tm mod = do
    putStrLn
        "   Running with OrcJIT (Broken for me. If working for you, please tell me!!)"
    -- loadLibraryPermanently Nothing
    --     >>= \b -> putStrLn $ "   load self: " ++ show (not b)
    -- loadLibraryPermanently
    --         (Just "../foreign-core/target/release/libcarth_foreign_core.so")
    --     >>= \b -> putStrLn $ "   load foreign core: " ++ show (not b)
    resolvers <- newIORef Map.empty
    let linkingResolver key = fmap (Map.! key) (readIORef resolvers)
    session <- createExecutionSession
    linkLay <- newObjectLinkingLayer session linkingResolver
    compLay <- newIRCompileLayer linkLay tm
    let resolver symbol = do
            -- putStrLn ("Resolving symbol " ++ show symbol)
            findSymbol compLay symbol False
    withSymbolResolver session (SymbolResolver resolver) $ \resolverPtr ->
        withModuleKey session $ \modKey -> do
            modifyIORef' resolvers (Map.insert modKey resolverPtr)
            withModule compLay modKey mod $ do
                -- (putStrLn . ("add-int: " ++) . show)
                --     =<< getSymbolAddressInProcess
                --     =<< mangleSymbol compLay "add-int"
                mainSymbol <- mangleSymbol compLay "main"
                resolver mainSymbol >>= \case
                    Left err -> do
                        putStrLn "Error during JIT symbol resolution"
                        print err
                        exitFailure
                    Right (JITSymbol mainAddr _) ->
                        mkMain (castPtrToFunPtr (wordPtrToPtr mainAddr)) $> ()
    disposeCompileLayer compLay
    disposeLinkingLayer linkLay
    disposeExecutionSession session

-- | `writeLLVMAssemblyToFile` doesn't clear file contents before writing,
--   so this is a workaround.
writeLLVMAssemblyToFile' :: FilePath -> Module -> IO ()
writeLLVMAssemblyToFile' f m = do
    writeFile f ""
    writeLLVMAssemblyToFile (File f) m

withHostTargetMachinePIC :: (TargetMachine -> IO a) -> IO a
withHostTargetMachinePIC =
    withHostTargetMachine Reloc.PIC CodeModel.Default CodeGenOpt.None
