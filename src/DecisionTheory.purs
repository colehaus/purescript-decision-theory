module DecisionTheory where

import Prelude hiding ((>=),(>))

import Data.Foldable as Foldable
import Data.List as List
import Data.List.NonEmpty (NonEmptyList)
import Data.List.NonEmpty as NonEmpty
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Maybe as Maybe
import Data.Ord.Partial (class PartialOrd, (>=), (>))
import Data.Proportion (Proportion)
import Data.Proportion as Proportion
import Data.Semigroup.Foldable as Foldable1
import Partial.Unsafe (unsafePartial)
import Prelude as Prelude

type Row = NonEmptyList

dominatesWeakly :: forall cell. PartialOrd cell => Row cell -> Row cell -> Boolean
dominatesWeakly row1 row2 = Foldable.all ((==) true) (NonEmpty.zipWith (>=) row1 row2)

dominatesStrongly :: forall cell. PartialOrd cell => Row cell -> Row cell -> Boolean
dominatesStrongly row1 row2 =
    Foldable.all ((==) true) (NonEmpty.zipWith (>=) row1 row2) &&
    Foldable.any ((==) true) (NonEmpty.zipWith (>) row1 row2)

strengthen :: forall cell. (Row cell -> Row cell -> Boolean) -> Row cell -> Row cell -> Boolean
strengthen f row1 row2 = f row1 row2 && not (f row2 row1)

-- | A functionally identical variant of `dominatesStrongly` which emphasizes that it is the asymmetric version of `dominatesWeakly`
dominatesStrongly' :: forall cell. PartialOrd cell => Row cell -> Row cell -> Boolean
dominatesStrongly' = strengthen dominatesWeakly

leximin :: forall cell. Ord cell => Row cell -> Row cell -> Boolean
leximin row1 row2 =
    fromMaybe true <<< List.head <<< NonEmpty.mapMaybe keepNonEq $
    NonEmpty.zipWith compare (NonEmpty.sort row1) (NonEmpty.sort row2)
  where
    keepNonEq GT = Just true
    keepNonEq LT = Just false
    keepNonEq EQ = Nothing

maximin :: forall cell. Ord cell => Row cell -> Row cell -> Boolean
maximin row1 row2 = Foldable1.minimum row1 Prelude.>= Foldable1.minimum row2

maximax :: forall cell. Ord cell => Row cell -> Row cell -> Boolean
maximax row1 row2 = Foldable1.maximum row1 Prelude.>= Foldable1.maximum row2

-- | Functionally identical variant of `leximin` in which the implementation emphasizes the relationship between leximin and maximin
leximin' :: forall cell. Ord cell => Row cell -> Row cell -> Boolean
leximin' = ximin identity

-- | Functionally identical variant of `maximin` in which the implementation emphasizes the relationship between leximin and maximin
maximin' :: forall cell. Ord cell => Row cell -> Row cell -> Boolean
maximin' = ximin (NonEmpty.singleton <<< NonEmpty.head)

-- | Functionally identical variant of `maximax` in which the implementation emphasizes the relationship between leximin and maximax
maximax' :: forall cell. Ord cell => Row cell -> Row cell -> Boolean
maximax' = ximin (NonEmpty.singleton <<< NonEmpty.last)

-- | Helper function which is used to implement both `leximin'` and `maximin`'
ximin ::
  forall cell.
  Ord cell =>
  (forall a. NonEmptyList a -> NonEmptyList a) -> Row cell -> Row cell -> Boolean
ximin f row1 row2 =
    fromMaybe true <<< List.head <<< NonEmpty.mapMaybe keepNonEq <<< f $
    NonEmpty.zipWith compare (NonEmpty.sort row1) (NonEmpty.sort row2)
  where
    keepNonEq GT = Just true
    keepNonEq LT = Just false
    keepNonEq EQ = Nothing

optimismPessimism ::
  forall n. Ord n => Ring n => Proportion n -> Row n -> Row n -> Boolean
optimismPessimism α row1 row2 = val row1 >= val row2
  where
    val row =
      Proportion.unMk α * Foldable1.maximum row +
      (one - Proportion.unMk α) * Foldable1.minimum row

maximax'' :: forall n. Ord n => Ring n => NonEmptyList n -> NonEmptyList n -> Boolean
maximax'' = optimismPessimism (unsafePartial $ Maybe.fromJust $ Proportion.mk one)

maximin'' :: forall n. Ord n => Ring n => NonEmptyList n -> NonEmptyList n -> Boolean
maximin'' = optimismPessimism (unsafePartial $ Maybe.fromJust $ Proportion.mk zero)
