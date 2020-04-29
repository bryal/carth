{-# LANGUAGE ForeignFunctionInterface, OverloadedStrings, LambdaCase
           , OverloadedStrings #-}

module Compile (compile, run) where

import LLVM.Context
import LLVM.Module
import LLVM.Target
import LLVM.Analysis
import LLVM.OrcJIT
import LLVM.OrcJIT.LinkingLayer as LL
import LLVM.Linking
import LLVM.Internal.OrcJIT (MangledSymbol(..))
import qualified LLVM.Relocation as Reloc
import qualified LLVM.CodeModel as CodeModel
import qualified LLVM.CodeGenOpt as CodeGenOpt
import Data.ByteString.Short (toShort)
import Control.Monad
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

import Conf
import qualified Monomorphic
import Codegen


compile :: FilePath -> CompileConfig -> Monomorphic.Program -> IO ()
compile = handleProgram compileModule cDebug

run :: FilePath -> RunConfig -> Monomorphic.Program -> IO ()
run = handleProgram (const orcJitModule) rDebug

-- TODO: CodeGenOpt level
handleProgram
    :: (config -> TargetMachine -> Module -> IO ())
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
            f cfg tm mod

compileModule :: CompileConfig -> TargetMachine -> Module -> IO ()
compileModule cfg tm mod = do
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
    putStrLn "   Running with OrcJIT"
    putStrLn "   Loading symbols of running process"
    _ <- loadLibraryPermanently Nothing
    resolvers <- newIORef Map.empty
    let linkingResolver key = fmap (Map.! key) (readIORef resolvers)
    session <- createExecutionSession
    linkLay <- newObjectLinkingLayer session linkingResolver
    compLay <- newIRCompileLayer linkLay tm
    withSymbolResolver session (SymbolResolver (resolver linkLay))
        $ \resolverPtr -> withModuleKey session $ \modKey -> do
            modifyIORef' resolvers (Map.insert modKey resolverPtr)
            withModule compLay modKey mod $ do
                mangleSymbol compLay "main" >>= resolver linkLay >>= \case
                    Left err -> do
                        putStrLn "   Error during JIT symbol resolution"
                        print err
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
--   `addObjectFile`. We might be able to compile foreign-core to a .o file and
--   add it via this mechanism.
--
-- - `Linking.getSymbolAddressInProcess`: Looks in the address-space of the
--   running process. If we link with libcarth_foreign_core.so when building
--   carth, we can see the symbols with this. Cannot see `main` in the
--   compile-layer, which I guess makes sense -- why would `withModule` add it's
--   JITted symbols to the address-space of the carth process. Requires that the
--   symbols of the current process are made available first with
--   `Linking.loadLibraryPermanently Nothing`.
resolver
    :: ObjectLinkingLayer
    -> MangledSymbol
    -> IO (Either JITSymbolError JITSymbol)
resolver linkLay (symb@(MangledSymbol bsymb)) = do
    let ssymb = show bsymb
    putStrLn ("   Resolving " ++ ssymb ++ " in linking layer")
    LL.findSymbol linkLay (toShort bsymb) False >>= \case
        Right jitsym -> do
            putStrLn ("   Resolved " ++ ssymb)
            pure (Right jitsym)
        Left _ -> do
            putStrLn $ "   Error resolving " ++ ssymb ++ " in linking layer"
            putStrLn "   Resolving in running process"
            addr <- getSymbolAddressInProcess symb
            if addr == 0
                then do
                    let e =
                            "Error resolving " ++ ssymb ++ " in running process"
                    putStrLn ("   " ++ e)
                    pure (Left (JITSymbolError (fromString e)))
                else do
                    putStrLn ("   Resolved " ++ ssymb)
                    let flags = JITSymbolFlags
                            { jitSymbolWeak = False
                            , jitSymbolCommon = False
                            , jitSymbolAbsolute = False
                            , jitSymbolExported = True
                            }
                    pure (Right (JITSymbol addr flags))

-- | `writeLLVMAssemblyToFile` doesn't clear file contents before writing,
--   so this is a workaround.
writeLLVMAssemblyToFile' :: FilePath -> Module -> IO ()
writeLLVMAssemblyToFile' f m = do
    writeFile f ""
    writeLLVMAssemblyToFile (File f) m

withHostTargetMachinePIC :: (TargetMachine -> IO a) -> IO a
withHostTargetMachinePIC =
    withHostTargetMachine Reloc.PIC CodeModel.Default CodeGenOpt.None
