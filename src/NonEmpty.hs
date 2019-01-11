module NonEmpty (NonEmpty (..), intersperse1, intercalate1, map1, nonEmptyToList, nonEmpty) where

import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty (..), nonEmpty)
import Data.Composition
import Control.Monad
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen

instance Arbitrary a => Arbitrary (NonEmpty a) where
  arbitrary = liftM2 (:|) arbitrary (choose (0, 4) >>= flip vectorOf arbitrary)

intersperse1 :: a -> NonEmpty a -> NonEmpty a
intersperse1 = NonEmpty.intersperse

intercalate1 :: [a] -> NonEmpty [a] -> [a]
intercalate1 = concat .* intersperse1

map1 :: (a -> b) -> NonEmpty a -> NonEmpty b
map1 = NonEmpty.map

nonEmptyToList :: NonEmpty a -> [a]
nonEmptyToList = NonEmpty.toList
