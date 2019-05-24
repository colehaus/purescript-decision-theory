module DecisionTheory.Properties where

import Prelude

import Data.HashSet.Multi (MultiSet)
import Data.Hashable (class Hashable)
import Data.List (List(..))
import Data.List.NonEmpty (NonEmptyList(..))
import Data.List.NonEmpty as NonEmpty
import Data.Maybe (Maybe)
import Data.NonEmpty (NonEmpty(..))
import Data.Ord.Partial (class PartialOrd)
import Data.Ordering as Ordering
import Data.Tuple (Tuple(..))

import DecisionTheory.Ignorance
import DecisionTheory.Utility


columnDuplication ::
  forall cell.
  Hashable cell =>
  (NonEmpty MultiSet (Tuple cell cell) -> Boolean) ->
  NonEmpty MultiSet (Tuple cell cell) -> Boolean
columnDuplication rule actions =
  rule actions == rule (neListToNeMultiSet $ NonEmpty.zip (dupHead a) (dupHead b))
  where
   Tuple a b = NonEmpty.unzip <<< neMultiSetToNeList $ actions
   dupHead (NonEmptyList (NonEmpty x xs)) = NonEmptyList (NonEmpty x (x `Cons` xs))

columnLinearity ::
  forall cell.
  Hashable cell => Semiring cell =>
  (NonEmpty MultiSet (Tuple cell cell) -> Boolean) ->
  NonEmpty MultiSet (Tuple cell cell) -> cell -> Boolean
columnLinearity rule actions n =
  rule actions == rule (neListToNeMultiSet $ NonEmpty.zip (mapHead (_ + n) a) (mapHead (_ + n) b))
  where
   Tuple a b = NonEmpty.unzip <<< neMultiSetToNeList $ actions
   mapHead f (NonEmptyList (NonEmpty x xs)) = NonEmptyList (NonEmpty (f x) xs)

rowSymmetry ::
  forall cell.
  Hashable cell =>
  (NonEmpty MultiSet (Tuple cell cell) -> Maybe Ordering) ->
  NonEmpty MultiSet (Tuple cell cell) -> Boolean
rowSymmetry rule actions =
  rule actions == (Ordering.invert <$> rule (neListToNeMultiSet $ NonEmpty.zip b a))
  where
    Tuple a b = NonEmpty.unzip <<< neMultiSetToNeList $ actions

implies :: Boolean -> Boolean -> Boolean
implies antecedent consequent =
  if antecedent
  then consequent
  else true

strictDominance ::
  forall cell.
  PartialOrd cell =>
  (NonEmpty MultiSet (Tuple cell cell) -> Boolean) -> NonEmpty MultiSet (Tuple cell cell) -> Boolean
strictDominance rule actions =
  dominatesStrongly actions `implies` rule actions

intervalScale ::
  forall cell.
  Hashable cell => Semiring cell =>
  (NonEmpty MultiSet (Tuple cell cell) -> Boolean) ->
  NonEmpty MultiSet (Tuple cell cell) -> cell -> cell -> Boolean
intervalScale rule actions add mult =
  rule actions == rule (neListToNeMultiSet $ NonEmpty.zip (transform <$> a) (transform <$> b))
  where
    transform n = mult * n + add
    Tuple a b = NonEmpty.unzip <<< neMultiSetToNeList $ actions
