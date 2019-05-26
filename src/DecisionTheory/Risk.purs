module DecisionTheory.Risk where

import Prelude

import Data.Array as Array
import Data.Foldable as Foldable
import Data.HashSet.Multi (MultiSet)
import Data.HashSet.Multi as MultiSet
import Data.Hashable (class Hashable, hash)
import Data.NonEmpty (NonEmpty)
import Data.NonEmpty as NonEmpty
import Data.Proportion (Proportion)
import Data.Proportion as Proportion
import Data.Tuple (Tuple(..))

maximizesExpectedUtility ::
  forall cell prob.
  Ord cell => Hashable cell => Semiring cell => Hashable prob =>
  (Proportion prob -> cell) ->
  NonEmpty MultiSet (Tuple (HashProp prob) (Tuple cell cell)) -> Boolean
maximizesExpectedUtility toCell rows =
  Foldable.sum row1 >=
  Foldable.sum row2
  where
    asArray = MultiSet.toRepeatingArray <<< NonEmpty.fromNonEmpty MultiSet.insert $ rows
    expect (Tuple (MkHashProp p) (Tuple r1 r2)) = Tuple (toCell p * r1) (toCell p * r2)
    Tuple row1 row2 = Array.unzip $ expect <$> asArray

newtype HashProp n = MkHashProp (Proportion n)
derive newtype instance eqHashProp :: Eq n => Eq (HashProp n)
instance hashablebHashProp :: Hashable n => Hashable (HashProp n) where
  hash (MkHashProp p) = hash <<< Proportion.unMk $ p
