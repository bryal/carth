{-# LANGUAGE LambdaCase #-}

module SystemSpec where

import Data.Data
import Data.Functor
import Control.Monad
import System.Directory
import System.FilePath
import Data.List
import Test.Hspec
import System.IO.Silently

import Misc
import Parse
import Check
import Compile
import Monomorphize
import qualified Monomorphic
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
            result <- runIO $ parse (d </> f)
            it (dropExtension f) $ shouldSatisfy (fmap typecheck result) $ \case
                Right (Left e) -> show (toConstr e) == expectedErr
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

frontend :: FilePath -> IO (Maybe Monomorphic.Program)
frontend f = parse f <&> \case
    Left _ -> Nothing
    Right ast -> fmap monomorphize (rightToMaybe (typecheck ast))
