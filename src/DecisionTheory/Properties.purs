module DecisionTheory.Properties where

import Prelude

import Data.List (List(..))
import Data.List.NonEmpty (NonEmptyList(..))
import Data.List.NonEmpty as NonEmpty
import Data.Maybe (Maybe)
import Data.NonEmpty (NonEmpty(..))
import Data.Ord.Partial (class PartialOrd)
import Data.Ordering as Ordering
import Data.Tuple (Tuple(..))

import DecisionTheory.Ignorance

columnDuplication ::
  forall cell.
  (NonEmptyList (Tuple cell cell) -> Boolean) -> NonEmptyList (Tuple cell cell) -> Boolean
columnDuplication rule actions =
  rule actions == rule (NonEmpty.zip (dupHead a) (dupHead b))
  where
   Tuple a b = NonEmpty.unzip actions
   dupHead (NonEmptyList (NonEmpty x xs)) = NonEmptyList (NonEmpty x (x `Cons` xs))

columnLinearity ::
  forall cell.
  Eq Boolean => Semiring cell =>
  (NonEmptyList (Tuple cell cell) -> Boolean) ->
  NonEmptyList (Tuple cell cell) -> cell -> Boolean
columnLinearity rule actions n =
  rule actions == rule (NonEmpty.zip (mapHead (_ + n) a) (mapHead (_ + n) b))
  where
   Tuple a b = NonEmpty.unzip actions
   mapHead f (NonEmptyList (NonEmpty x xs)) = NonEmptyList (NonEmpty (f x) xs)

rowSymmetry ::
  forall cell.
  (NonEmptyList (Tuple cell cell) -> Maybe Ordering) -> NonEmptyList (Tuple cell cell) -> Boolean
rowSymmetry rule actions =
  rule actions == (Ordering.invert <$> rule (NonEmpty.zip b a))
  where
    Tuple a b = NonEmpty.unzip actions

columnSymmetry ::
  forall cell.
  (NonEmptyList (Tuple cell cell) -> Boolean) -> NonEmptyList (Tuple cell cell) -> Boolean
columnSymmetry rule actions =
  rule actions == rule (NonEmpty.zip (NonEmpty.reverse a) (NonEmpty.reverse b))
  where
    Tuple a b = NonEmpty.unzip actions

implies :: Boolean -> Boolean -> Boolean
implies antecedent consequent =
  if antecedent
  then consequent
  else true

strictDominance ::
  forall cell.
  PartialOrd cell =>
  (NonEmptyList (Tuple cell cell) -> Boolean) -> NonEmptyList (Tuple cell cell) -> Boolean
strictDominance rule actions =
  dominatesStrongly actions `implies` rule actions

intervalScale ::
  forall cell.
  Semiring cell =>
  (NonEmptyList (Tuple cell cell) -> Boolean) ->
  NonEmptyList (Tuple cell cell) -> cell -> cell -> Boolean
intervalScale rule actions add mult =
  rule actions == rule (NonEmpty.zip (transform <$> a) (transform <$> b))
  where
    transform n = mult * n + add
    Tuple a b = NonEmpty.unzip actions
