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
import Data.Proportion.Internal (Proportion(..))
import Data.Table as Table
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Partial.Unsafe (unsafePartial)
import Test.QuickCheck ((<?>), (===))
import Test.QuickCheck as QuickCheck
import Test.QuickCheck.Gen as Gen
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck')
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (run)

quickCheck'' :: forall t2. QuickCheck.Testable t2 => t2 -> Aff Unit
quickCheck'' = quickCheck' 2000

main :: Effect Unit
main = run [consoleReporter] do
  describe "Domination" do
    it "works for domination" do
      (ne 9 [ 9 ]) `dominatesWeakly` (ne 1 [ 1 ]) `shouldEqual` true
    it "works for non-domination" do
      (ne 1 [ 1 ]) `dominatesWeakly` (ne 0 [ 9 ]) `shouldEqual` false
    it "is antisymmetric" do
      quickCheck'' $ \(MkListPair a b) ->
        Prop.antisymmetric dominatesWeakly a b <?> (show [ a, b ])
    propGroup dominatesWeakly
    describe "Strong" do
      it "works for domination" do
        (ne 9 [ 9 ]) `dominatesStrongly` (ne 1 [ 1 ]) `shouldEqual` true
      it "works for non-domination" do
        (ne 1 [ 1 ]) `dominatesStrongly` (ne 1 [ 1 ]) `shouldEqual` false
      it "implies weak domination" do
        quickCheck'' $ \(MkListPair a b) ->
          if a `dominatesStrongly` b
          then a `dominatesWeakly` b <?> (show [ a, b ])
          else QuickCheck.Success
      it "is `dominatesWeakly` `strengthen`ed" do
        quickCheck'' $ \(MkListPair a b) ->
          dominatesStrongly a b === strengthen dominatesWeakly a b
  describe "Leximin" do
    it "works for superiority at worst outcome" do
      (ne 2 [ 5, 9 ]) `leximin` (ne 9 [ 6, 1 ]) `shouldEqual` true
    it "works for superiority at best outcome" do
      (ne 1 [ 5, 9 ]) `leximin` (ne 8 [ 5, 1 ]) `shouldEqual` true
    it "works for equality" do
      (ne 1 [ 5, 9 ]) `leximin` (ne 9 [ 5, 1 ]) `shouldEqual` true
    it "works for inferiority" do
      (ne 1 [ 5, 9 ]) `leximin` (ne 9 [ 6, 1 ]) `shouldEqual` false
    propGroup leximin
    it "is `leximin'`" do
      quickCheck'' $ \(MkListPair a b) ->
        leximin a b === leximin' a b
  describe "Maximin" do
    it "works for superiority" do
      (ne 2 [ 5, 9 ]) `maximin` (ne 9 [ 6, 1 ]) `shouldEqual` true
    it "works for equality" do
      (ne 1 [ 5, 10 ]) `maximin` (ne 1 [ 9, 6 ]) `shouldEqual` true
    it "works for inferiority" do
      (ne 1 [ 6, 9 ]) `maximin` (ne 9 [ 5, 2 ]) `shouldEqual` false
    it "is `maximin'`" do
      quickCheck'' $ \(MkListPair a b) ->
        maximin a b === maximin' a b
    it "is `maximin''`" do
      quickCheck'' $ \(MkListPair a b) ->
        maximin a b === maximin'' a b
    propGroup maximin
    describe "Strong" do
      it "implies leximin" do
        quickCheck'' $ \(MkListPair a b) ->
          if strengthen maximin a b
          then strengthen leximin a b <?> (show [ a, b ])
          else QuickCheck.Success
  describe "Optimism-Pessimism" do
    let conv = map (Int.toNumber <<< Newtype.unwrap)
    it "is reflexive" do
      quickCheck'' $ \(MkArbProportion α) (a :: NonEmptyList SmallNat) ->
        Prop.reflexive (optimismPessimism α) (conv a) <?> (show $ Tuple α a)
    it "is transitive" do
      quickCheck'' $ \(MkArbProportion α) (MkListTriple a b c) ->
        Prop.transitive (optimismPessimism α) (conv a) (conv b) (conv c) <?> (show $ Tuple α [ a, b, c ])
    describe "Strong" do
      it "is transitive" do
        quickCheck'' $ \(MkArbProportion α) (MkListTriple a b c) ->
          Prop.transitive (strengthen (optimismPessimism α)) (conv a) (conv b) (conv c) <?> (show [ a, b, c ])
      it "is asymmetric" do
        quickCheck'' $ \(MkArbProportion α) (MkListPair a b) ->
          Prop.asymmetric (strengthen (optimismPessimism α)) (conv a) (conv b) <?> (show [ a, b ])
  describe "minimaxRegret" do
    it "works for example cases" do
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


propGroup :: (Row SmallNat -> Row SmallNat -> Boolean) -> Spec Unit
propGroup rule = do
  it "is reflexive" do
    quickCheck'' $ \(a :: NonEmptyList SmallNat) ->
      Prop.reflexive rule a <?> (show a)
  it "is transitive" do
    quickCheck'' $ \(MkListTriple a b c) ->
      Prop.transitive rule a b c <?> (show [ a, b, c ])
  describe "Strong" do
    it "is transitive" do
      quickCheck'' $ \(MkListTriple a b c) ->
        Prop.transitive (strengthen rule) a b c <?> (show [ a, b, c ])
    it "is asymmetric" do
      quickCheck'' $ \(MkListPair a b) ->
        Prop.asymmetric (strengthen rule) a b <?> (show [ a, b ])


fromRightEx :: forall l r. Either l r -> r
fromRightEx x = unsafePartial $ Either.fromRight x

ne :: forall a. a -> Array a -> NonEmptyList a
ne x y = NonEmptyList (NonEmpty x (List.fromFoldable y))

newtype SmallNat = MkSmallNat Int
derive instance eqSmallNat :: Eq SmallNat
derive instance ordSmallNat :: Ord SmallNat
derive instance genericSmallNat :: Generic SmallNat _
derive instance newtypeSmallNat :: Newtype SmallNat _
derive newtype instance semiringSmallNat :: Semiring SmallNat
derive newtype instance ringSmallNat :: Ring SmallNat
instance showSmallNat :: Show SmallNat where
  show (MkSmallNat i) = show i
instance arbitrarySmallInt :: QuickCheck.Arbitrary SmallNat where
  arbitrary = MkSmallNat <$> Gen.chooseInt 1 10

data ListPair = MkListPair (NonEmptyList SmallNat) (NonEmptyList SmallNat)
instance arbitraryListPair :: QuickCheck.Arbitrary ListPair where
  arbitrary = do
    l <- arrayToList <$> Gen.arrayOf1 QuickCheck.arbitrary
    r <- toNonEmpty <$> Gen.vectorOf (Foldable.length l) QuickCheck.arbitrary
    pure $ MkListPair l r
    where
      arrayToList (NonEmpty a as) = NonEmptyList (NonEmpty a (List.fromFoldable as))
      toNonEmpty a = unsafePartial $ Maybe.fromJust <<< NonEmpty.fromFoldable $ a

data ListTriple = MkListTriple (NonEmptyList SmallNat) (NonEmptyList SmallNat) (NonEmptyList SmallNat)
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
