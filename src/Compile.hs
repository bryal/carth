module Compile (compile) where

import LLVM.Context
import LLVM.Module
import LLVM.Target
import Data.Function.Slip

import Annot (Program(..))
import qualified Mono
import Codegen

-- TODO: Verify w LLVM.Analysis.verify :: Module -> IO ()
-- TODO: CodeGenOpt level
compile :: FilePath -> Mono.MProgram -> IO ()
compile moduleFilePath (Program main defs) =
    withContext $ (slipr withModuleFromAST)
        (genModule moduleFilePath main defs)
        (withHostTargetMachine . slipr writeObjectToFile (File "out.o"))
