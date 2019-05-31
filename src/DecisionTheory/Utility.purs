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
import Data.Maybe (Maybe, fromJust)
import Data.NonEmpty (NonEmpty(..))
import Data.Proportion as Proportion
import Data.Tuple (Tuple)
import DecisionTheory.Risk (HashProp(..))
import Partial.Unsafe (unsafePartialBecause)

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

unzipNeMultiSet ::
  forall a b.
  NonEmpty MultiSet (Tuple a b) -> Tuple (NonEmptyList a) (NonEmptyList b)
unzipNeMultiSet = NonEmpty.unzip <<< neMultiSetToNeList

neMultiSetMap ::
  forall a b.
  Hashable b =>
  (a -> b) -> NonEmpty MultiSet a -> NonEmpty MultiSet b
neMultiSetMap f (NonEmpty a as) = NonEmpty (f a) (MultiSet.map f as)

unsafeMkHashProp :: forall n. Ord n => Semiring n => n -> HashProp n
unsafeMkHashProp p =
  MkHashProp <<<
  unsafePartialBecause "Statically known to be valid `Proportion`" $
  fromJust <<< Proportion.mk $ p
