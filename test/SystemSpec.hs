module SystemSpec where

import Prelude hiding (lex)

import Data.Functor
import Control.Monad
import Control.Monad.Except
import System.Directory
import System.FilePath
import Data.List
import Test.Hspec
import System.IO.Silently

import Misc
import Lex
import Macro
import Parse
import qualified Parsed
import Check
import Compile
import Monomorphize
import Lower
import qualified Low as Ast
import Conf

spec :: Spec
spec = do
    describe "Good programs run with expected output" $ do
        let d = "test/tests/good"
        fs <- runIO $ listDirectory d <&> filter isSourceFile
        forM_ fs $ \f -> do
            expectedOut <- runIO $ fmap
                (unlines . map (drop 3) . takeWhile (isPrefixOf ";; ") . lines)
                (readFile (d </> f))
            it (dropExtension f) $ shouldReturn (run' (d </> f)) expectedOut
    describe "Bad programs don't typecheck" $ do
        let d = "test/tests/bad"
        fs <- runIO $ listDirectory d <&> filter isSourceFile
        forM_ fs $ \f -> do
            expectedErr <- runIO $ fmap (drop 3 . head . lines) (readFile (d </> f))
            result <- runIO $ lexAndParse (d </> f)
            it (dropExtension f) $ shouldSatisfy (fmap typecheck result) $ \case
                Just (Left e) -> head (words (show e)) == expectedErr
                _ -> False
    describe "Examples compile" $ do
        let d = "examples"
        fs <- runIO $ listDirectory d <&> filter isSourceFile
        forM_ fs $ \f -> do
            it (dropExtension f) $ shouldReturn (compile' (d </> f)) True
    describe "Benchmarks compile" $ do
        let d = "test/bench"
        fs <- runIO $ listDirectory d <&> filter isSourceFile
        forM_ fs $ \f -> do
            it (dropExtension f) $ shouldReturn (compile' (d </> f)) True

isSourceFile :: FilePath -> Bool
isSourceFile f = let e = takeExtension f in e == ".carth" || e == ".org"

run' :: FilePath -> IO String
run' f =
    let cfg = defaultRunConfig f
    in  frontend f >>= \case
            Nothing -> error "Program failed to pass through frontend"
            Just ast -> capture_ (run f cfg ast)

compile' :: FilePath -> IO Bool
compile' f =
    let cfg = defaultCompileConfig f (dropExtension f)
    in  frontend f >>= \case
            Nothing -> pure False
            Just ast -> compile f cfg ast $> True

frontend :: FilePath -> IO (Maybe Ast.Program)
frontend f = lexAndParse f <&> \case
    Nothing -> Nothing
    Just ast -> fmap (lower . monomorphize) (rightToMaybe (typecheck ast))

lexAndParse :: FilePath -> IO (Maybe Parsed.Program)
lexAndParse f = fmap rightToMaybe (runExceptT (lex' f >>= expandMacros' >>= parse''))
  where
    lex' = withExceptT (const ()) . lex
    expandMacros' = withExceptT (const ()) . liftEither . runExcept . expandMacros
    parse'' = withExceptT (const ()) . liftEither . runExcept . parse
