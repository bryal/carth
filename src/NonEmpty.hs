{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module NonEmpty
    ( NonEmpty(..)
    , intersperse1
    , intercalate1
    , precalate1
    , map1
    , nonEmptyToList
    , nonEmpty
    )
where

import Data.Composition
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty(..), nonEmpty)

import Misc

intersperse1 :: a -> NonEmpty a -> NonEmpty a
intersperse1 = NonEmpty.intersperse

intercalate1 :: [a] -> NonEmpty [a] -> [a]
intercalate1 = concat .* intersperse1

precalate1 :: [a] -> NonEmpty [a] -> [a]
precalate1 prefix = (prefix ++) . intercalate1 prefix

map1 :: (a -> b) -> NonEmpty a -> NonEmpty b
map1 = NonEmpty.map

nonEmptyToList :: NonEmpty a -> [a]
nonEmptyToList = NonEmpty.toList

instance FreeVars a v => FreeVars (NonEmpty a) v where
    freeVars = freeVars . nonEmptyToList
    boundVars = boundVars . nonEmptyToList
