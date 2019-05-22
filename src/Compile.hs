module Compile (compile) where

import qualified LLVM.Context as Ctx
import qualified LLVM.Module as Mod
import qualified LLVM.Target as Targ

import Annot (Program(..))
import qualified Mono
import Codegen

compile :: FilePath -> Mono.MProgram -> IO ()
compile moduleFilePath (Program main defs) = Ctx.withContext $ \ctx ->
    Mod.withModuleFromAST ctx (genModule moduleFilePath main defs) $ \mod' ->
        Targ.withHostTargetMachine
            $ \targ -> Mod.writeObjectToFile targ (Mod.File "out.o") mod'
