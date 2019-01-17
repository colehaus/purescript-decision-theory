module DecisionTheory where

import Prelude hiding ((>=), (>))

import Data.Foldable as Foldable
import Data.Maybe (Maybe(..))
import Data.List.NonEmpty (NonEmptyList)
import Data.List.NonEmpty as NonEmpty
import Data.Ord.Partial (class PartialOrd, (>=), (>))
import Data.Tuple (Tuple(..))
import Data.Table (Table)
import Data.Table as Table

dominatesWeakly ::
  forall rowId columnId cell column.
  Eq rowId => PartialOrd cell =>
  Table rowId columnId cell (NonEmptyList cell) column -> rowId -> rowId -> Maybe Boolean
dominatesWeakly t rId1 rId2 =
  case Tuple (Table.row t rId1) (Table.row t rId2) of
    Tuple Nothing _ -> Nothing
    Tuple _ Nothing -> Nothing
    Tuple (Just r1) (Just r2) ->
      Just <<< Foldable.all ((==) true) $ NonEmpty.zipWith (>=) r1 r2

dominatesStrongly ::
  forall rowId columnId cell column.
  Eq rowId => PartialOrd cell =>
  Table rowId columnId cell (NonEmptyList cell) column -> rowId -> rowId -> Maybe Boolean
dominatesStrongly t rId1 rId2 =
  case Tuple (Table.row t rId1) (Table.row t rId2) of
    Tuple Nothing _ -> Nothing
    Tuple _ Nothing -> Nothing
    Tuple (Just r1) (Just r2) ->
      Just $
        Foldable.all ((==) true) (NonEmpty.zipWith (>=) r1 r2) &&
        Foldable.any ((==) true) (NonEmpty.zipWith (>) r1 r2)
