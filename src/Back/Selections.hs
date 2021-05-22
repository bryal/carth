module Back.Selections (Select (..), Selections, newSelections, select, selectVarBindings) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Word
import Control.Monad

import Misc
import Back.Low

type Selections a = Map Access a

class Select m a where
    selectAs :: Span -> [Type] -> a -> m a
    selectSub :: Span -> Word32 -> a -> m a
    selectDeref :: a -> m a

newSelections :: a -> Selections a
newSelections x = Map.singleton Obj x

select :: (Monad m, Select m a) => Access -> Selections a -> m (a, Selections a)
select selector selections = case Map.lookup selector selections of
    Just a -> pure (a, selections)
    Nothing -> do
        (a, selections') <- case selector of
            Obj -> ice "select: Obj not in selections"
            As x span' ts -> do
                (a', s') <- select x selections
                a'' <- selectAs span' ts a'
                pure (a'', s')
            Sel i span' x -> do
                (a', s') <- select x selections
                a'' <- selectSub span' i a'
                pure (a'', s')
            ADeref x -> do
                (a', s') <- select x selections
                a'' <- selectDeref a'
                pure (a'', s')
        pure (a, Map.insert selector a selections')

selectVarBindings
    :: (Monad m, Select m a) => Selections a -> VarBindings -> m [(TypedVar, a)]
selectVarBindings selections = fmap fst . foldM
    (\(bs', ss) (x, s) -> do
        (a, ss') <- select s ss
        pure ((x, a) : bs', ss')
    )
    ([], selections)
