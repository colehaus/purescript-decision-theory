module Test.Main where

import DecisionTheory.Ignorance
import Prelude

import Control.Algebra.Properties as Prop
import Data.Either (Either, fromRight)
import Data.Either as Either
import Data.Foldable as Foldable
import Data.Generic.Rep (class Generic)
import Data.Int as Int
import Data.List (List(..))
import Data.List as List
import Data.List.NonEmpty (NonEmptyList(..))
import Data.List.NonEmpty as NonEmpty
import Data.Map as Map
import Data.Maybe as Maybe
import Data.Newtype (class Newtype)
import Data.Newtype as Newtype
import Data.NonEmpty (NonEmpty(..))
import Data.Ordering as Ord
import Data.Proportion as Proportion
import Data.Proportion.Internal (Proportion(..))
import Data.Rational (Rational)
import Data.Rational as Rational
import Data.Table as Table
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Partial.Unsafe (unsafePartial)
import Test.QuickCheck (Result, (<?>), (===))
import Test.QuickCheck as QuickCheck
import Test.QuickCheck.Gen as Gen
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck')
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (run)

quickCheck'' :: forall t2. QuickCheck.Testable t2 => t2 -> Aff Unit
quickCheck'' = quickCheck' 2000

implies :: Boolean -> Result -> Result
implies antecedent consequent =
  if antecedent
  then consequent
  else QuickCheck.Success

main :: Effect Unit
main = run [consoleReporter] do
  describe "Domination" do
    it "works for domination" do
      (ne 9 [ 9 ]) `listCurry dominatesWeakly` (ne 1 [ 1 ]) `shouldEqual` true
    it "works for non-domination" do
      (ne 1 [ 1 ]) `listCurry dominatesWeakly` (ne 0 [ 9 ]) `shouldEqual` false
    it "is antisymmetric" do
      quickCheck'' $ \(MkListPair a b) ->
        Prop.antisymmetric (listCurry dominatesWeakly) a b <?> show [ a, b ]
    propGroup dominatesWeakly
    describe "Strong" do
      it "works for domination" do
        (ne 9 [ 9 ]) `listCurry dominatesStrongly` (ne 1 [ 1 ]) `shouldEqual` true
      it "works for non-domination" do
        (ne 1 [ 1 ]) `listCurry dominatesStrongly` (ne 1 [ 1 ]) `shouldEqual` false
      it "implies weak domination" do
        quickCheck'' $ \(MkListPair a b) ->
          (a `listCurry dominatesStrongly` b) `implies`
          (a `listCurry dominatesWeakly` b <?> show [ a, b ])
      it "is `dominatesWeakly` `strengthen`ed" do
        quickCheck'' $ \(MkListPair a b) ->
          (listCurry dominatesStrongly) a b == listCurry (strengthen dominatesWeakly) a b <?> show [a, b]
  describe "Leximin" do
    it "works for superiority at worst outcome" do
      (ne 2 [ 5, 9 ]) `listCurry leximin` (ne 9 [ 6, 1 ]) `shouldEqual` true
    it "works for superiority at best outcome" do
      (ne 1 [ 5, 9 ]) `listCurry leximin` (ne 8 [ 5, 1 ]) `shouldEqual` true
    it "works for equality" do
      (ne 1 [ 5, 9 ]) `listCurry leximin` (ne 9 [ 5, 1 ]) `shouldEqual` true
    it "works for inferiority" do
      (ne 1 [ 5, 9 ]) `listCurry leximin` (ne 9 [ 6, 1 ]) `shouldEqual` false
    propGroup leximin
    it "is `leximin'`" do
      quickCheck'' $ \(MkListPair a b) ->
        listCurry leximin a b === listCurry leximin' a b
  describe "Maximin" do
    it "works for superiority" do
      (ne 2 [ 5, 9 ]) `listCurry maximin` (ne 9 [ 6, 1 ]) `shouldEqual` true
    it "works for equality" do
      (ne 1 [ 5, 10 ]) `listCurry maximin` (ne 1 [ 9, 6 ]) `shouldEqual` true
    it "works for inferiority" do
      (ne 1 [ 6, 9 ]) `listCurry maximin` (ne 9 [ 5, 2 ]) `shouldEqual` false
    it "is `maximin'`" do
      quickCheck'' $ \(MkListPair a b) ->
        listCurry maximin a b === listCurry maximin' a b
    it "is `maximin''`" do
      quickCheck'' $ \(MkListPair a b) ->
        listCurry maximin a b === listCurry (maximin'' (MkSmallNum <<< Rational.fromInt <<< Int.round)) a b
    it "is invariant under column duplication" do
      let dupHead (NonEmptyList (NonEmpty x xs)) = NonEmptyList (NonEmpty x (x `Cons` xs))
          prop2SmallNum = MkSmallNum <<< Rational.fromInt <<< Int.round <<< Proportion.unMk
      quickCheck'' $ \(MkListPair a b) ->
        a `listCurry maximin` b === dupHead a `listCurry maximin` dupHead b
    propGroup maximin
    describe "Strong" do
      it "implies leximin" do
        quickCheck'' $ \(MkListPair a b) ->
          if listCurry (strengthen maximin) a b
          then listCurry (strengthen leximin) a b <?> show [ a, b ]
          else QuickCheck.Success
  describe "Optimism-Pessimism" do
    let conv = map (Rational.toNumber <<< Newtype.unwrap)
    it "is reflexive" do
      quickCheck'' $ \(MkArbProportion α) (a :: NonEmptyList SmallNum) ->
        Prop.reflexive (listCurry (optimismPessimism identity α)) (conv a) <?> show (Tuple α a)
    describe "Strong" do
      it "is transitive" do
        quickCheck'' $ \(MkArbProportion α) (MkListTriple a b c) ->
          Prop.transitive (listCurry (strengthen (optimismPessimism identity α))) (conv a) (conv b) (conv c) <?> show [ a, b, c ]
      it "is asymmetric" do
        quickCheck'' $ \(MkArbProportion α) (MkListPair a b) ->
          Prop.asymmetric (listCurry (strengthen (optimismPessimism identity α))) (conv a) (conv b) <?> show [ a, b ]
  describe "minimaxRegret" do
    it "works for an example" do
      let cells =
            [ Tuple (Tuple "row1" "column1") 12
            , Tuple (Tuple "row1" "column2") 8
            , Tuple (Tuple "row1" "column3") 20
            , Tuple (Tuple "row1" "column4") 20
            , Tuple (Tuple "row2" "column1") 10
            , Tuple (Tuple "row2" "column2") 15
            , Tuple (Tuple "row2" "column3") 16
            , Tuple (Tuple "row2" "column4") 8
            , Tuple (Tuple "row3" "column1") 30
            , Tuple (Tuple "row3" "column2") 6
            , Tuple (Tuple "row3" "column3") 25
            , Tuple (Tuple "row3" "column4") 14
            , Tuple (Tuple "row4" "column1") 20
            , Tuple (Tuple "row4" "column2") 4
            , Tuple (Tuple "row4" "column3") 30
            , Tuple (Tuple "row4" "column4") 10
            ]
      minimaxRegret (unsafePartial $ fromRight <<< Table.mk $ Map.fromFoldable cells) `shouldEqual` NonEmptyList (NonEmpty "row3" Nil)
  describe "indifference" do
    it "works for an example" do
      (ne 1.1 [ 1.0 ]) `listCurry (indifference Proportion.unMk)` (ne 1.2 [ 0.8 ]) `shouldEqual` true
    it "is linear in columns" do
      let mapHead f (NonEmptyList (NonEmpty x xs)) = NonEmptyList (NonEmpty (f x) xs)
          prop2SmallNum = MkSmallNum <<< Rational.fromInt <<< Int.round <<< Proportion.unMk
          indifference' a b = listCurry (indifference prop2SmallNum) a b
      quickCheck'' $ \(MkListPair a b) c ->
        let a' = mapHead (_ + c) a
            b' = mapHead (_ + c) b
        in
          (a `indifference'` b ==
          a' `indifference'` b') <?> show (Tuple [a, b, a', b'] c)

propGroup :: (NonEmptyList (Tuple SmallNum SmallNum) -> Boolean) -> Spec Unit
propGroup rule = do
  it "is invariant under relabeling (symmetric)" do
    quickCheck'' $ \(MkListPair a b) ->
      listCurry (weakRelationToOrdering rule) a b === Ord.invert <$> listCurry (weakRelationToOrdering rule) b a
  it "is reflexive" do
    quickCheck'' $ \(a :: NonEmptyList SmallNum) ->
      Prop.reflexive (listCurry rule) a <?> show a
  it "is transitive" do
    quickCheck'' $ \(MkListTriple a b c) ->
      Prop.transitive (listCurry rule) a b c <?> show [ a, b, c ]
  it "obeys strict dominance" do
    quickCheck'' $ \(MkListPair a b) ->
      (a `listCurry dominatesStrongly` b) `implies`
      ((a `listCurry rule` b) <?> show [ a, b ])
  it "works on an interval scale" do
    quickCheck'' $ \(MkListPair a b) add mult ->
      (a `listCurry rule` b == ((\n -> mult * n + add) <$> a) `listCurry rule` ((\n -> mult * n + add) <$> b)) <?> show (Tuple [ a, b ] [ add, mult ])
  describe "Strong" do
    it "is transitive" do
      quickCheck'' $ \(MkListTriple a b c) ->
        Prop.transitive (listCurry (strengthen rule)) a b c <?> show [ a, b, c ]
    it "is asymmetric" do
      quickCheck'' $ \(MkListPair a b) ->
        Prop.asymmetric (listCurry (strengthen rule)) a b <?> show [ a, b ]

listCurry ::
  forall cell res.
  (NonEmptyList (Tuple cell cell) -> res) ->
  NonEmptyList cell -> NonEmptyList cell -> res
listCurry rule row1 row2 = rule (NonEmpty.zip row1 row2)

fromRightEx :: forall l r. Either l r -> r
fromRightEx x = unsafePartial $ Either.fromRight x

ne :: forall a. a -> Array a -> NonEmptyList a
ne x y = NonEmptyList (NonEmpty x (List.fromFoldable y))

newtype SmallNum = MkSmallNum Rational
derive instance eqSmallNum :: Eq SmallNum
derive instance ordSmallNum :: Ord SmallNum
derive instance genericSmallNum :: Generic SmallNum _
derive instance newtypeSmallNum :: Newtype SmallNum _
derive newtype instance semiringSmallNum :: Semiring SmallNum
derive newtype instance ringSmallNum :: Ring SmallNum
instance showSmallNum :: Show SmallNum where
  show (MkSmallNum i) = show i
instance arbitrarySmallNum :: QuickCheck.Arbitrary SmallNum where
  arbitrary = MkSmallNum <<< Rational.fromInt <$> Gen.chooseInt 1 10

data ListPair = MkListPair (NonEmptyList SmallNum) (NonEmptyList SmallNum)
instance arbitraryListPair :: QuickCheck.Arbitrary ListPair where
  arbitrary = do
    l <- arrayToList <$> Gen.arrayOf1 QuickCheck.arbitrary
    r <- toNonEmpty <$> Gen.vectorOf (Foldable.length l) QuickCheck.arbitrary
    pure $ MkListPair l r
    where
      arrayToList (NonEmpty a as) = NonEmptyList (NonEmpty a (List.fromFoldable as))
      toNonEmpty a = unsafePartial $ Maybe.fromJust <<< NonEmpty.fromFoldable $ a

data ListTriple = MkListTriple (NonEmptyList SmallNum) (NonEmptyList SmallNum) (NonEmptyList SmallNum)
instance arbitraryListTriple :: QuickCheck.Arbitrary ListTriple where
  arbitrary = do
    l <- arrayToList <$> Gen.arrayOf1 QuickCheck.arbitrary
    m <- toNonEmpty <$> Gen.vectorOf (Foldable.length l) QuickCheck.arbitrary
    r <- toNonEmpty <$> Gen.vectorOf (Foldable.length l) QuickCheck.arbitrary
    pure $ MkListTriple l m r
    where
      arrayToList (NonEmpty a as) = NonEmptyList (NonEmpty a (List.fromFoldable as))
      toNonEmpty a = unsafePartial $ Maybe.fromJust <<< NonEmpty.fromFoldable $ a

newtype ArbProportion = MkArbProportion (Proportion Number)

instance arbitraryProportian :: QuickCheck.Arbitrary ArbProportion where
  arbitrary = MkArbProportion <<< MkProportion <$> Gen.uniform
