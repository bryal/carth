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

spec :: Spec
spec = do
    -- describe "Good programs" $ do
    --     it "produce expected output" $ shouldSatisfy True id
    describe "Bad programs don't typecheck" $ do
        let d = "test/tests/bad"
        fs <- runIO $ listDirectory d <&> filter (isExtensionOf "carth")
        forM_ fs $ \f -> do
            expectedErr <- runIO $ fmap (drop 3 . head . lines) (readFile (d </> f))
            result <- runIO $ parse (d </> f)
            it (dropExtension f) $ shouldSatisfy (fmap typecheck result) $ \case
                Right (Left e) -> show (toConstr e) == expectedErr
                _ -> False
