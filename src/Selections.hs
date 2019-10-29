{-# LANGUAGE LambdaCase, TupleSections #-}

module Selections (Selections, newSelections, select, selectVarBindings) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Word
import Control.Monad

import Misc
import MonoAst


type Selections a = Map Access a


newSelections :: a -> Selections a
newSelections x = Map.singleton Obj x

select
    :: (Show a, Monad m)
    => ([Type] -> a -> m a)
    -> (Word32 -> a -> m a)
    -> Access
    -> Selections a
    -> m (a, Selections a)
select conv sub selector selections = case Map.lookup selector selections of
    Just a -> pure (a, selections)
    Nothing -> do
        (a, selections') <- case selector of
            Obj -> ice "select: Obj not in selections"
            As x ts -> do
                (a', s') <- select conv sub x selections
                a'' <- conv ts a'
                pure (a'', s')
            Sel i x -> do
                (a', s') <- select conv sub x selections
                a'' <- sub i a'
                pure (a'', s')
        pure (a, Map.insert selector a selections')

selectVarBindings
    :: (Show a, Monad m)
    => ([Type] -> a -> m a)
    -> (Word32 -> a -> m a)
    -> Selections a
    -> VarBindings
    -> m [(TypedVar, a)]
selectVarBindings conv sub selections = fmap fst . foldM
    (\(bs', ss) (x, s) -> do
        (a, ss') <- select conv sub s ss
        pure ((x, a) : bs', ss')
    )
    ([], selections)
