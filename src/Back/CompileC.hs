-- | Generation of LLVM IR code from our monomorphic AST.
module Back.CompileC (compile) where

import Back.Low as Low
import Conf
import Misc

compile :: FilePath -> CompileConfig -> Low.Program -> IO ()
compile f _ _ = putStrLn "C backend not yet implemented" *> abort f
