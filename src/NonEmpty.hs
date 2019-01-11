module NonEmpty (NonEmpty (..), intersperse1, intercalate1, map1, nonEmptyToList, nonEmpty) where

import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty (..), nonEmpty)
import Data.Composition

intersperse1 = NonEmpty.intersperse
intercalate1 = concat .* intersperse1
map1 = NonEmpty.map
nonEmptyToList = NonEmpty.toList
