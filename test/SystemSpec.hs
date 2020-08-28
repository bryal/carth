{-# LANGUAGE LambdaCase #-}

module SystemSpec where

import Data.Data
import Data.Functor
import Control.Monad
import System.Directory
import System.FilePath
import Test.Hspec

import Parse
import Check
import Compile
import Monomorphize
import Conf

spec :: Spec
spec = do
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
    describe "Bad programs don't typecheck" $ do
        let d = "test/tests/bad"
        fs <- runIO $ listDirectory d <&> filter isSourceFile
        forM_ fs $ \f -> do
            expectedErr <- runIO $ fmap (drop 3 . head . lines) (readFile (d </> f))
            result <- runIO $ parse (d </> f)
            it (dropExtension f) $ shouldSatisfy (fmap typecheck result) $ \case
                Right (Left e) -> show (toConstr e) == expectedErr
                _ -> False

isSourceFile :: FilePath -> Bool
isSourceFile f = let e = takeExtension f in e == ".carth" || e == ".org"

compile' :: FilePath -> IO Bool
compile' f =
    let cfg = defaultCompileConfig f (dropExtension f)
    in  Parse.parse f >>= \case
            Left _ -> pure False
            Right ast -> case typecheck ast of
                Left _ -> pure False
                Right ann -> compile f cfg (monomorphize ann) $> True
