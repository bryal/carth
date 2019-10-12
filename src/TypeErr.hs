{-# LANGUAGE LambdaCase, FlexibleContexts #-}

module TypeErr (TypeErr(..), otherErr, posErr) where

import Control.Monad.Except
import Data.Composition

import Misc
import SrcPos

data TypeErr
    = OtherErr String
    | PosErr SrcPos String

instance Pretty TypeErr where
    pretty' _ = \case
        OtherErr msg -> "Error: " ++ msg
        PosErr (SrcPos p) msg -> sourcePosPretty p ++ ": Error: " ++ msg

otherErr :: MonadError TypeErr m => String -> m a
otherErr = throwError . OtherErr

posErr :: MonadError TypeErr m => SrcPos -> String -> m a
posErr = throwError .* PosErr
