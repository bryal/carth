{-# LANGUAGE ForeignFunctionInterface, OverloadedStrings, LambdaCase
           , OverloadedStrings #-}

module Compile (compile, run) where

import LLVM.Context
import LLVM.Module
import LLVM.Target
import LLVM.Analysis
import LLVM.OrcJIT
import LLVM.OrcJIT.CompileLayer as CL
import LLVM.Linking
import LLVM.PassManager
import LLVM.Exception
import qualified LLVM.Relocation as Reloc
import qualified LLVM.CodeModel as CodeModel
import qualified LLVM.CodeGenOpt as CodeGenOpt
import Control.Monad
import Control.Monad.Catch
import System.FilePath
import System.Process
import System.Exit
import Data.Int
import Data.Functor
import Data.IORef
import Data.String
import qualified Data.Map as Map
import Foreign.Ptr
import Prelude hiding (mod)

import Misc
import Conf
import qualified Monomorphic
import Codegen


compile :: FilePath -> CompileConfig -> Monomorphic.Program -> IO ()
compile = handleProgram compileModule

run :: FilePath -> RunConfig -> Monomorphic.Program -> IO ()
run = handleProgram orcJitModule

handleProgram
    :: Config cfg
    => (cfg -> TargetMachine -> Module -> IO ())
    -> FilePath
    -> cfg
    -> Monomorphic.Program
    -> IO ()
handleProgram f file cfg pgm = withContext $ \ctx ->
    -- When `--debug` is given, only -O1 optimize the code. Otherwise, optimize
    -- by -O2. No point in going further to -O3, as those optimizations are
    -- expensive and seldom actually improve the performance in a statistically
    -- significant way.
    --
    -- A minimum optimization level of -O1 ensures that all sibling calls are
    -- optimized, even if we don't use a calling convention like `fastcc` that
    -- can optimize any tail call.
    let optLvl = if (getDebug cfg) then CodeGenOpt.Less else CodeGenOpt.Default
    in
        withHostTargetMachinePIC optLvl $ \tm -> do
            layout <- getTargetMachineDataLayout tm
            verbose cfg ("   Generating LLVM")
            let amod = codegen layout file pgm
            withModuleFromAST ctx amod $ \mod -> do
                verbose cfg ("   Verifying LLVM")
                when (getDebug cfg) $ writeLLVMAssemblyToFile' ".dbg.ll" mod
                catch (verify mod) $ \case
                    VerifyException msg ->
                        ice $ "LLVM verification exception:\n" ++ msg
                withPassManager (optPasses optLvl tm) $ \passman -> do
                    verbose cfg "   Optimizing"
                    _ <- runPassManager passman mod
                    when (getDebug cfg)
                        $ writeLLVMAssemblyToFile' ".dbg.opt.ll" mod
                    f cfg tm mod

compileModule :: CompileConfig -> TargetMachine -> Module -> IO ()
compileModule cfg tm mod = do
    let exefile = cOutfile cfg
        ofile = replaceExtension exefile "o"
    verbose cfg "   Writing object"
    writeObjectToFile tm (File ofile) mod
    verbose cfg ("   Linking")
    callProcess
        (cCompiler cfg)
        [ "-o"
        , exefile
        , ofile
        , "-l:libcarth_foreign_core.a"
        , "-lsigsegv"
        , "-ldl"
        , "-lpthread"
        , "-lm"
        ]

foreign import ccall "dynamic"
  mkMain :: FunPtr (IO Int32) -> IO Int32

orcJitModule :: RunConfig -> TargetMachine -> Module -> IO ()
orcJitModule cfg tm mod = do
    verbose cfg "   Running with OrcJIT"
    let libs = ["libsigsegv.so", "libcarth_foreign_core.so"]
    forM_ libs $ \lib -> do
        verbose cfg $ "   Loading symbols of " ++ lib
        r <- loadLibraryPermanently (Just lib)
        when r (putStrLn ("   Error loading " ++ lib) *> exitFailure)
    resolvers <- newIORef Map.empty
    let linkingResolver key = fmap (Map.! key) (readIORef resolvers)
    session <- createExecutionSession
    linkLay <- newObjectLinkingLayer session linkingResolver
    compLay <- newIRCompileLayer linkLay tm
    let resolver' = resolver compLay
    withSymbolResolver session (SymbolResolver resolver') $ \resolverPtr ->
        withModuleKey session $ \modKey -> do
            modifyIORef' resolvers (Map.insert modKey resolverPtr)
            withModule compLay modKey mod $ do
                mangleSymbol compLay "main" >>= resolver' >>= \case
                    Left err -> do
                        putStrLn "   Error during JIT symbol resolution"
                        putStrLn ("   error: " ++ show err)
                        exitFailure
                    Right (JITSymbol mainAddr _) ->
                        mkMain (castPtrToFunPtr (wordPtrToPtr mainAddr)) $> ()
    disposeCompileLayer compLay
    disposeLinkingLayer linkLay
    disposeExecutionSession session

-- Following are some useful things to know regarding symbol resolution when it
-- comes to JIT, LLVM, and OrcJIT. I'm not sure about all of this, so take it
-- with a grain of salt.
--
-- - `CompileLayer.findSymbol`: Only looks in the compile-layer, which includes
--   our compiled LLVM modules, but not linked object code, or linked shared
--   libraries.
--
-- - `LinkingLayer.findSymbol`: Looks in the linking-layer, a superset of the
--   compile-layer that includes all object code added to the layer with
--   `addObjectFile`.
--
-- - `Linking.getSymbolAddressInProcess`: Looks in the address-space of the
--   running process, which includes all shared object code added with
--   `Linking.loadLibraryPermanently`. Disjoint from the compile and linking
--   layer.
resolver
    :: CompileLayer cl
    => cl
    -> MangledSymbol
    -> IO (Either JITSymbolError JITSymbol)
resolver compLay symb =
    let
        flags = JITSymbolFlags
            { jitSymbolWeak = False
            , jitSymbolCommon = False
            , jitSymbolAbsolute = False
            , jitSymbolExported = True
            }
        err = fromString ("Error resolving symbol: " ++ show symb)
        findInLlvmModules = CL.findSymbol compLay symb False
        findInSharedObjects = getSymbolAddressInProcess symb <&> \addr ->
            if addr == 0
                then Left (JITSymbolError err)
                else Right (JITSymbol addr flags)
    in findInLlvmModules >>= \case
        Right js -> pure (Right js)
        Left _ -> findInSharedObjects

-- | `writeLLVMAssemblyToFile` doesn't clear file contents before writing,
--   so this is a workaround.
writeLLVMAssemblyToFile' :: FilePath -> Module -> IO ()
writeLLVMAssemblyToFile' f m = do
    writeFile f ""
    writeLLVMAssemblyToFile (File f) m

withHostTargetMachinePIC :: CodeGenOpt.Level -> (TargetMachine -> IO a) -> IO a
withHostTargetMachinePIC = withHostTargetMachine Reloc.PIC CodeModel.Default

optPasses :: CodeGenOpt.Level -> TargetMachine -> PassSetSpec
optPasses level tm =
    let
        levelN = case level of
            CodeGenOpt.None -> 0
            CodeGenOpt.Less -> 1
            CodeGenOpt.Default -> 2
            CodeGenOpt.Aggressive -> 3
    in
        CuratedPassSetSpec
            { optLevel = Just levelN
            , sizeLevel = Nothing
            , unitAtATime = Nothing
            , simplifyLibCalls = Nothing
            , loopVectorize = Nothing
            , superwordLevelParallelismVectorize = Nothing
            , useInlinerWithThreshold = Nothing
            , dataLayout = Nothing
            , targetLibraryInfo = Nothing
            , targetMachine = Just tm
            }
