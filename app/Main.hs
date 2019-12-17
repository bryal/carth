{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Data.Functor

import Misc
import qualified TypeErr
import qualified Ast
import qualified DesugaredAst
import qualified MonoAst
import Check
import Config
import Compile
import Mono
import qualified Parse

main :: IO ()
main = uncurry compileFile =<< getConfig

compileFile :: FilePath -> CompileConfig -> IO ()
compileFile f cfg = do
    putStrLn ("   Compiling " ++ f ++ "\n")
    parse f >>= typecheck' f >>= monomorphize' >>= compile f cfg

parse :: FilePath -> IO Ast.Program
parse f = Parse.parse f >>= \case
    Left e -> putStrLn (formatParseErr e) >> abort f
    Right p -> writeFile "out.parsed" (pretty p) $> p
  where
    formatParseErr e =
        let ss = lines e in (unlines ((head ss ++ " Error:") : tail ss))

typecheck' :: FilePath -> Ast.Program -> IO DesugaredAst.Program
typecheck' f p = case typecheck p of
    Left e -> TypeErr.printErr e >> abort f
    Right p -> writeFile "out.checked" (show p) $> p

monomorphize' :: DesugaredAst.Program -> IO MonoAst.Program
monomorphize' p = do
    let p' = monomorphize p
    writeFile "out.mono" (show p')
    pure p'
