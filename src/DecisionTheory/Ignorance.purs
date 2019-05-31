module DecisionTheory.Ignorance where

import DecisionTheory.Risk
import DecisionTheory.Utility
import Prelude hiding ((>=),(>))

import Data.Array as Array
import Data.Either (fromRight)
import Data.Foldable as Foldable
import Data.HashMap (HashMap)
import Data.HashMap as HashMap
import Data.HashSet (HashSet)
import Data.HashSet as HashSet
import Data.HashSet.Multi (MultiSet)
import Data.HashSet.Multi as MultiSet
import Data.Hashable (class Hashable)
import Data.Int as Int
import Data.List as List
import Data.List.NonEmpty (NonEmptyList)
import Data.List.NonEmpty as NEL
import Data.List.NonEmpty as NonEmpty
import Data.Maybe (Maybe(..), fromJust, fromMaybe)
import Data.NonEmpty (NonEmpty(..))
import Data.Ord.Partial (class PartialOrd, (>), (>=))
import Data.Proportion (Proportion)
import Data.Proportion as Proportion
import Data.Semigroup.Foldable as Foldable1
import Data.Table (Table)
import Data.Table as Table
import Data.Tuple (Tuple(..))
import Data.Tuple as Tuple
import Partial.Unsafe (unsafePartialBecause)
import Prelude as Prelude

zipActions ::
  forall state cell.
  Hashable state => Hashable cell =>
  HashMap state cell -> HashMap state cell -> MultiSet (Tuple cell cell)
zipActions m1 m2 =
  MultiSet.fromFoldable <<< HashMap.values $ HashMap.intersectionWith Tuple m1 m2

type PairOfRows cell = NonEmpty MultiSet (Tuple cell cell)

dominatesWeakly :: forall cell. PartialOrd cell => PairOfRows cell -> Boolean
dominatesWeakly rows = Foldable.and (NonEmpty.zipWith (>=) row1 row2)
  where
    Tuple row1 row2 = unzipNeMultiSet rows

dominatesStrongly :: forall cell. PartialOrd cell => PairOfRows cell -> Boolean
dominatesStrongly rows =
  Foldable.and (NonEmpty.zipWith (>=) row1 row2) &&
  Foldable.or (NonEmpty.zipWith (>) row1 row2)
  where
    Tuple row1 row2 = unzipNeMultiSet rows

strengthen ::
  forall cell.
  Hashable cell =>
  (PairOfRows cell -> Boolean) ->
  PairOfRows cell -> Boolean
strengthen f rows = f rows && not (f $ map Tuple.swap rows)
  where
    map g (NonEmpty x xs) = NonEmpty (g x) (MultiSet.map g xs)

-- | A functionally identical variant of `dominatesStrongly` in which the implementation
-- emphasizes that it is the asymmetric version of `dominatesWeakly`
dominatesStrongly' ::
  forall cell.
  Hashable cell =>
  PartialOrd cell =>
  PairOfRows cell -> Boolean
dominatesStrongly' = strengthen dominatesWeakly

leximin :: forall cell. Ord cell => PairOfRows cell -> Boolean
leximin rows =
    fromMaybe true <<< List.head <<< NonEmpty.mapMaybe keepNonEq $
    NonEmpty.zipWith compare (NonEmpty.sort row1) (NonEmpty.sort row2)
  where
    Tuple row1 row2 = unzipNeMultiSet rows
    keepNonEq GT = Just true
    keepNonEq LT = Just false
    keepNonEq EQ = Nothing

maximin :: forall cell. Ord cell => PairOfRows cell -> Boolean
maximin rows = Foldable1.minimum row1 Prelude.>= Foldable1.minimum row2
  where
    Tuple row1 row2 = unzipNeMultiSet rows

maximax :: forall cell. Ord cell => PairOfRows cell -> Boolean
maximax rows = Foldable1.maximum row1 Prelude.>= Foldable1.maximum row2
  where
    Tuple row1 row2 = unzipNeMultiSet rows

-- | Functionally identical variant of `leximin` in which the implementation emphasizes the
-- relationship between leximin and maximin
leximin' :: forall cell. Ord cell => PairOfRows cell -> Boolean
leximin' = ximin identity

-- | Functionally identical variant of `maximin` in which the implementation emphasizes the
-- relationship between leximin and maximin
maximin' :: forall cell. Ord cell => PairOfRows cell -> Boolean
maximin' = ximin (NonEmpty.singleton <<< NonEmpty.head)

-- | Functionally identical variant of `maximax` in which the implementation emphasizes the
-- relationship between leximin and maximax
maximax' :: forall cell. Ord cell => PairOfRows cell -> Boolean
maximax' = ximin (NonEmpty.singleton <<< NonEmpty.last)

-- | Helper function which is used to implement both `leximin'` and `maximin`'
ximin ::
  forall cell.
  Ord cell =>
  (forall a. NonEmptyList a -> NonEmptyList a) -> PairOfRows cell -> Boolean
ximin f rows =
    fromMaybe true <<< List.head <<< NonEmpty.mapMaybe keepNonEq <<< f $
    NonEmpty.zipWith compare (NonEmpty.sort row1) (NonEmpty.sort row2)
  where
    Tuple row1 row2 = unzipNeMultiSet rows
    keepNonEq GT = Just true
    keepNonEq LT = Just false
    keepNonEq EQ = Nothing

optimismPessimism ::
  forall n cell.
  Ord cell => Semiring cell => Ring n =>
  (n -> cell) -> Proportion n -> PairOfRows cell -> Boolean
optimismPessimism toCell α rows = value row1 >= value row2
  where
    Tuple row1 row2 = unzipNeMultiSet rows
    value row =
      toCell (Proportion.unMk α) * Foldable1.maximum row +
      toCell (one - Proportion.unMk α) * Foldable1.minimum row

maximax'' ::
  forall cell.
  Ord cell => Semiring cell =>
  (Number -> cell) -> PairOfRows cell -> Boolean
maximax'' toCell =
  optimismPessimism toCell <<<
  unsafePartialBecause "Statically known to be valid `Proportion`" $
  fromJust <<< Proportion.mk $
  one

maximin'' ::
  forall cell.
  Ord cell => Semiring cell =>
  (Number -> cell) -> PairOfRows cell -> Boolean
maximin'' toCell =
  optimismPessimism toCell <<<
  unsafePartialBecause "Statically known to be valid `Proportion`"  $
  fromJust <<< Proportion.mk $
  zero

-- | Like turning `>=` into `compare`
weakRelationToOrdering ::
  forall cell.
  Hashable cell =>
  (PairOfRows cell -> Boolean) ->
  PairOfRows cell -> Maybe Ordering
weakRelationToOrdering f rows =
  case Tuple (f rows) (f <<< neListToNeMultiSet $ NonEmpty.zip row2 row1) of
    Tuple true true -> Just EQ
    Tuple true false -> Just GT
    Tuple false true -> Just LT
    Tuple false false -> Nothing
  where
    Tuple row1 row2 = unzipNeMultiSet rows

-- | Find all rows which return `true` when compared to every other other row by the given
-- relation
extremal ::
  forall rowId columnId cell.
  Hashable cell => Hashable columnId => Hashable rowId =>
  (PairOfRows cell -> Boolean) ->
  Table rowId columnId cell -> HashSet rowId
extremal relation tbl =
  HashSet.fromArray <<< HashMap.keys <<<
  HashMap.filter (\r1 -> Foldable.all (\r2 -> relation $ munge r1 r2) cellsOfRows) $
  rows
  where
    munge r1 r2 =
      unsafePartialBecause "Grouping always produces non-empty inner collections" $
      fromJust <<< neMultiSet $
      zipActions r1 r2
    rowId m =
      Table.rowId <<<
      unsafePartialBecause "Grouping always produces non-empty inner collections" $
      fromJust <<< Array.head <<<
      HashMap.keys $
      m
    cellsOfRows =
      unsafePartialBecause "Grouping always produces non-empty inner collections" $
      fromJust <<< NEL.fromFoldable $
      rows
    rows = Table.rows' tbl

minimaxRegret ::
  forall rowId columnId cell.
  Hashable cell => Hashable columnId => Hashable rowId =>
  Ord cell => Ring cell =>
  Table rowId columnId cell -> NonEmpty HashSet rowId
minimaxRegret tbl =
  fromJustMin <<< neSet <<< extremal minimax $ regrets
  where
    regrets = fromRightRegret <<< Table.mapColumns regretify $ tbl
      where
        regretify cells = map (best - _) cells
          where
            best = fromJustZero <<< Foldable.maximum $ cells
    minimax rows = Foldable1.maximum row1 Prelude.<= Foldable1.maximum row2
      where
        Tuple row1 row2 = unzipNeMultiSet rows
    fromJustZero x =
      unsafePartialBecause
        """If the table is empty,
        there will be zero columns instead of columns with zero cells""" $ fromJust x
    fromRightRegret x =
      unsafePartialBecause "`Regretify` preserves table validity" $ fromRight x
    fromJustMin x =
      unsafePartialBecause "There should always be at least one minimum"  $ fromJust x

indifference ::
  forall cell.
  Hashable cell =>
  Ord cell => Semiring cell =>
  (Proportion Number -> cell) -> PairOfRows cell -> Boolean
indifference toCell rows =
  maximizesExpectedUtility toCell <<<
  neMultiSetMap (Tuple prob) $ rows
  where
    prob = unsafeMkHashProp $ 1.0 / Int.toNumber (Foldable.length rows)
