module DecisionTheory.Utility where

import Prelude

import Data.Array as Array
import Data.HashSet (HashSet)
import Data.HashSet as HashSet
import Data.HashSet.Multi (MultiSet)
import Data.HashSet.Multi as MultiSet
import Data.Hashable (class Hashable)
import Data.List as List
import Data.List.NonEmpty (NonEmptyList(..))
import Data.List.NonEmpty as NonEmpty
import Data.Maybe (Maybe)
import Data.NonEmpty (NonEmpty(..))

neMultiSetToNeList :: forall a. NonEmpty MultiSet a -> NonEmptyList a
neMultiSetToNeList (NonEmpty a m) =
  NonEmpty.cons' a (List.fromFoldable <<< MultiSet.toRepeatingArray $ m)

neListToNeMultiSet :: forall a. Hashable a => NonEmptyList a -> NonEmpty MultiSet a
neListToNeMultiSet (NonEmptyList (NonEmpty a l)) = NonEmpty a (MultiSet.fromFoldable l)

neMultiSet :: forall a. Hashable a => MultiSet a -> Maybe (NonEmpty MultiSet a)
neMultiSet =
  map (\x -> NonEmpty x.head (MultiSet.fromFoldable x.tail)) <<< Array.uncons <<<
  MultiSet.toRepeatingArray

neSet :: forall a. Hashable a => HashSet a -> Maybe (NonEmpty HashSet a)
neSet =
  map (\x -> NonEmpty x.head (HashSet.fromFoldable x.tail)) <<< Array.uncons <<<
  HashSet.toArray
