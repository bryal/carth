{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module Misc where

import qualified Data.Set as Set
import Data.Set (Set)

ice :: String -> a
ice = error . ("Internal Compiler Error: " ++)

class Ord v => FreeVars a v where
    freeVars :: a -> Set v
    boundVars :: a -> Set v
    boundVars = const Set.empty

instance FreeVars a v => FreeVars [a] v where
    freeVars = Set.unions . map freeVars
    boundVars = Set.unions . map boundVars
