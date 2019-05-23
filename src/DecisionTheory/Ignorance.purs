module DecisionTheory.Ignorance where

import DecisionTheory.Risk
import Prelude hiding ((>=),(>))

import Data.Either (fromRight)
import Data.Foldable as Foldable
import Data.Int as Int
import Data.List (List)
import Data.List as List
import Data.List.NonEmpty (NonEmptyList)
import Data.List.NonEmpty as NonEmpty
import Data.Maybe (Maybe(..), fromJust, fromMaybe)
import Data.Maybe as Maybe
import Data.Ord.Partial (class PartialOrd, (>=), (>))
import Data.Proportion (Proportion)
import Data.Proportion as Proportion
import Data.Semigroup.Foldable as Foldable1
import Data.Semigroup.Foldable as SemiFold
import Data.Table (Table)
import Data.Table as Table
import Data.Tuple (Tuple(..), fst, snd)
import Data.Tuple as Tuple
import Data.Unfoldable1 as Unfold1
import Partial.Unsafe (unsafePartialBecause)
import Prelude as Prelude

dominatesWeakly :: forall cell. PartialOrd cell => NonEmptyList (Tuple cell cell) -> Boolean
dominatesWeakly rows = Foldable.all ((==) true) (NonEmpty.zipWith (>=) row1 row2)
  where
    Tuple row1 row2 = NonEmpty.unzip rows

dominatesStrongly :: forall cell. PartialOrd cell => NonEmptyList (Tuple cell cell) -> Boolean
dominatesStrongly rows =
  Foldable.all ((==) true) (NonEmpty.zipWith (>=) row1 row2) &&
  Foldable.any ((==) true) (NonEmpty.zipWith (>) row1 row2)
  where
    Tuple row1 row2 = NonEmpty.unzip rows

strengthen ::
  forall cell.
  (NonEmptyList (Tuple cell cell) -> Boolean) -> NonEmptyList (Tuple cell cell) -> Boolean
strengthen f rows = f rows && not (f $ map Tuple.swap rows)

-- | A functionally identical variant of `dominatesStrongly` in which the implementation emphasizes that it is the asymmetric version of `dominatesWeakly`
dominatesStrongly' :: forall cell. PartialOrd cell => NonEmptyList (Tuple cell cell) -> Boolean
dominatesStrongly' = strengthen dominatesWeakly

leximin :: forall cell. Ord cell => NonEmptyList (Tuple cell cell) -> Boolean
leximin rows =
    fromMaybe true <<< List.head <<< NonEmpty.mapMaybe keepNonEq $
    NonEmpty.zipWith compare (NonEmpty.sort row1) (NonEmpty.sort row2)
  where
    Tuple row1 row2 = NonEmpty.unzip rows
    keepNonEq GT = Just true
    keepNonEq LT = Just false
    keepNonEq EQ = Nothing

maximin :: forall cell. Ord cell => NonEmptyList (Tuple cell cell) -> Boolean
maximin rows = Foldable1.minimum row1 Prelude.>= Foldable1.minimum row2
  where
    Tuple row1 row2 = NonEmpty.unzip rows

maximax :: forall cell. Ord cell => NonEmptyList (Tuple cell cell) -> Boolean
maximax rows = Foldable1.maximum row1 Prelude.>= Foldable1.maximum row2
  where
    Tuple row1 row2 = NonEmpty.unzip rows

-- | Functionally identical variant of `leximin` in which the implementation emphasizes the relationship between leximin and maximin
leximin' :: forall cell. Ord cell => NonEmptyList (Tuple cell cell) -> Boolean
leximin' = ximin identity

-- | Functionally identical variant of `maximin` in which the implementation emphasizes the relationship between leximin and maximin
maximin' :: forall cell. Ord cell => NonEmptyList (Tuple cell cell) -> Boolean
maximin' = ximin (NonEmpty.singleton <<< NonEmpty.head)

-- | Functionally identical variant of `maximax` in which the implementation emphasizes the relationship between leximin and maximax
maximax' :: forall cell. Ord cell => NonEmptyList (Tuple cell cell)-> Boolean
maximax' = ximin (NonEmpty.singleton <<< NonEmpty.last)

-- | Helper function which is used to implement both `leximin'` and `maximin`'
ximin ::
  forall cell.
  Ord cell =>
  (forall a. NonEmptyList a -> NonEmptyList a) -> NonEmptyList (Tuple cell cell) -> Boolean
ximin f rows =
    fromMaybe true <<< List.head <<< NonEmpty.mapMaybe keepNonEq <<< f $
    NonEmpty.zipWith compare (NonEmpty.sort row1) (NonEmpty.sort row2)
  where
    Tuple row1 row2 = NonEmpty.unzip rows
    keepNonEq GT = Just true
    keepNonEq LT = Just false
    keepNonEq EQ = Nothing

optimismPessimism ::
  forall n cell.
  Ord cell => Semiring cell => Ring n =>
  (n -> cell) -> Proportion n -> NonEmptyList (Tuple cell cell) -> Boolean
optimismPessimism toCell α rows = val row1 >= val row2
  where
    Tuple row1 row2 = NonEmpty.unzip rows
    val row =
      toCell (Proportion.unMk α) * Foldable1.maximum row +
      toCell (one - Proportion.unMk α) * Foldable1.minimum row

maximax'' ::
  forall cell.
  Ord cell => Semiring cell =>
  (Number -> cell) -> NonEmptyList (Tuple cell cell) -> Boolean
maximax'' toCell =
  optimismPessimism toCell $ unsafePartialBecause "Statically known to be valid `Proportion`" $ fromJust $ Proportion.mk one

maximin'' ::
  forall cell.
  Ord cell => Semiring cell =>
  (Number -> cell) -> NonEmptyList (Tuple cell cell) -> Boolean
maximin'' toCell =
  optimismPessimism toCell $ unsafePartialBecause "Statically known to be valid `Proportion`"  $ Maybe.fromJust $ Proportion.mk zero

-- | Like turning `>=` into `compare`
weakRelationToOrdering ::
  forall cell.
  (NonEmptyList (Tuple cell cell) -> Boolean) -> NonEmptyList (Tuple cell cell) -> Maybe Ordering
weakRelationToOrdering f rows =
  case Tuple (f $ NonEmpty.zip row1 row2) (f $ NonEmpty.zip row2 row1) of
    Tuple true true -> Just EQ
    Tuple true false -> Just GT
    Tuple false true -> Just LT
    Tuple false false -> Nothing
  where
    Tuple row1 row2 = NonEmpty.unzip rows

-- | Find all rows which return `true` when compared to every other other row by the given relation
extremal ::
  forall rowId columnId cell.
  Ord columnId => Ord rowId =>
  (NonEmptyList (Tuple cell cell) -> Boolean) -> Table rowId columnId cell -> List rowId
extremal relation tbl =
  map rowId <<< List.filter (\r1 -> List.all (\r2 -> relation (NonEmpty.zip (map snd r1) r2)) cellsOfRows) $ rows
  where
    rowId = fst <<< fst <<< NonEmpty.head
    cellsOfRows = map (map snd) rows
    rows = Table.rows tbl

minimaxRegret ::
  forall rowId columnId cell.
  Ord columnId => Ord rowId => Ord cell => Ring cell =>
  Table rowId columnId cell -> NonEmptyList rowId
minimaxRegret tbl =
  unsafePartialBecause "There should always be at least one minimum" $
  fromJust <<< NonEmpty.fromList <<<
  extremal minimax $ regrets
  where
    regrets =
      unsafePartialBecause "`Regretify` preserves table validity" $ fromRight $
      Table.mapColumns regretify tbl
    minimax rows = Foldable1.maximum row1 Prelude.<= Foldable1.maximum row2
      where
        Tuple row1 row2 = NonEmpty.unzip rows
    regretify cells = map (\c -> best - c) cells
      where
        best = SemiFold.maximum cells

indifference ::
  forall cell.
  Ord cell => Semiring cell =>
  (Proportion Number -> cell) -> NonEmptyList (Tuple cell cell) -> Boolean
indifference toCell rows =
  maximizesExpectedUtility toCell $ NonEmpty.zip (Unfold1.replicate1 len prob) rows
  where
    len = Foldable.length rows
    prob =
      unsafePartialBecause "Statically known to be valid `Proportion`" $
      fromJust $ Proportion.mk $ 1.0 / Int.toNumber len
