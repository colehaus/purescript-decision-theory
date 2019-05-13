module DecisionTheory.Risk where

import Prelude

import Data.Foldable as Foldable
import Data.List.NonEmpty (NonEmptyList)
import Data.List.NonEmpty as NonEmpty
import Data.Proportion (Proportion)
import Data.Tuple (Tuple(..))

maximizesExpectedUtility ::
  forall cell prob.
  Ord cell => Semiring cell =>
  (Proportion prob -> cell) ->
  NonEmptyList (Tuple (Proportion prob) (Tuple cell cell)) -> Boolean
maximizesExpectedUtility toCell rows =
  Foldable.sum (NonEmpty.zipWith (*) probs row1) >=
  Foldable.sum (NonEmpty.zipWith (*) probs row2)
  where
    Tuple probs' rows = NonEmpty.unzip rows
    probs = toCell <$> probs'
    Tuple row1 row2 = NonEmpty.unzip rows
