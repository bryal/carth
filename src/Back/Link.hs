module Back.Link (link) where

import System.FilePath
import System.Process

import Conf

link :: CompileConfig -> IO ()
link cfg = do
    let exefile = cOutfile cfg
        ofile = replaceExtension exefile "o"
    verbose cfg "   Linking"
    callProcess
        (cCompiler cfg)
        [ "-fuse-ld=" ++ cLinker cfg
        , "-o"
        , exefile
        , ofile
        , "-lcarth_std_rs"
        , "-lsigsegv"
        , "-ldl"
        , "-lpthread"
        , "-lm"
        , "-lgc"
        , "-lssl"
        , "-lcrypto"
        ]
