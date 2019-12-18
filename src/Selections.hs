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
    => (Span -> [Type] -> a -> m a)
    -> (Span -> Word32 -> a -> m a)
    -> (a -> m a)
    -> Access
    -> Selections a
    -> m (a, Selections a)
select conv sub deref selector selections =
    case Map.lookup selector selections of
        Just a -> pure (a, selections)
        Nothing -> do
            (a, selections') <- case selector of
                Obj -> ice "select: Obj not in selections"
                As x span' ts -> do
                    (a', s') <- select conv sub deref x selections
                    a'' <- conv span' ts a'
                    pure (a'', s')
                Sel i span' x -> do
                    (a', s') <- select conv sub deref x selections
                    a'' <- sub span' i a'
                    pure (a'', s')
                ADeref x -> do
                    (a', s') <- select conv sub deref x selections
                    a'' <- deref a'
                    pure (a'', s')
            pure (a, Map.insert selector a selections')

selectVarBindings
    :: (Show a, Monad m)
    => (Span -> [Type] -> a -> m a)
    -> (Span -> Word32 -> a -> m a)
    -> (a -> m a)
    -> Selections a
    -> VarBindings
    -> m [(TypedVar, a)]
selectVarBindings conv sub deref selections = fmap fst . foldM
    (\(bs', ss) (x, s) -> do
        (a, ss') <- select conv sub deref s ss
        pure ((x, a) : bs', ss')
    )
    ([], selections)
