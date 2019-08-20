{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module NonEmpty
    ( NonEmpty(..)
    , intersperse1
    , intercalate1
    , precalate1
    , map1
    , toList1
    , fromList1
    , nonEmpty
    )
where

import Data.Composition
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty(..), nonEmpty)

intersperse1 :: a -> NonEmpty a -> NonEmpty a
intersperse1 = NonEmpty.intersperse

intercalate1 :: [a] -> NonEmpty [a] -> [a]
intercalate1 = concat .* intersperse1

precalate1 :: [a] -> NonEmpty [a] -> [a]
precalate1 prefix = (prefix ++) . intercalate1 prefix

map1 :: (a -> b) -> NonEmpty a -> NonEmpty b
map1 = NonEmpty.map

toList1 :: NonEmpty a -> [a]
toList1 = NonEmpty.toList

fromList1 :: [a] -> NonEmpty a
fromList1 = NonEmpty.fromList
