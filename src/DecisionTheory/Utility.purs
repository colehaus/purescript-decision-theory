module DecisionTheory.Utility where

import Prelude

import Data.HashSet.Multi (MultiSet)
import Data.HashSet.Multi as MultiSet
import Data.Hashable (class Hashable)
import Data.List as List
import Data.List.NonEmpty (NonEmptyList(..))
import Data.List.NonEmpty as NonEmpty
import Data.NonEmpty (NonEmpty(..))

neMultiSetToNeList :: forall a. NonEmpty MultiSet a -> NonEmptyList a
neMultiSetToNeList (NonEmpty a m) =
  NonEmpty.cons' a (List.fromFoldable <<< MultiSet.toRepeatingArray $ m)

neListToNeMultiSet :: forall a. Hashable a => NonEmptyList a -> NonEmpty MultiSet a
neListToNeMultiSet (NonEmptyList (NonEmpty a l)) = NonEmpty a (MultiSet.fromFoldable l)
