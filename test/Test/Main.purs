module Test.Main where

import Prelude

import Data.Either (Either)
import Data.Either as Either
import Data.List (List)
import Data.List.NonEmpty (NonEmptyList)
import Data.List.NonEmpty as NEList
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafePartial)
import Data.Table as Table

import Effect (Effect)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (run)

import DecisionTheory

fromRightEx :: forall l r. Either l r -> r
fromRightEx x = unsafePartial $ Either.fromRight x

mk :: forall a. NonEmptyList a -> Maybe (List a)
mk = Just <<< NEList.toList

main :: Effect Unit
main = run [consoleReporter] do
  describe "Domination" do
    describe "Weak" do
      it "returns `Just true` for domination" do
        let cells =
              [ Tuple (Tuple "row1" "column1") 9
              , Tuple (Tuple "row1" "column2") 9
              , Tuple (Tuple "row2" "column1") 1
              , Tuple (Tuple "row2" "column2") 1
              ]
            table = fromRightEx $ Table.mk mk mk (Map.fromFoldable cells)
        dominatesWeakly table "row1" "row2" `shouldEqual` Just true
      it "returns `Just false` for non-domination" do
        let cells =
              [ Tuple (Tuple "row1" "column1") 1
              , Tuple (Tuple "row1" "column2") 1
              , Tuple (Tuple "row2" "column1") 9
              , Tuple (Tuple "row2" "column2") 9
              ]
            table = fromRightEx $ Table.mk mk mk (Map.fromFoldable cells)
        dominatesWeakly table "row1" "row2" `shouldEqual` Just false
      it "returns `Nothing` for missing rows" do
        let cells =
              [ Tuple (Tuple "row1" "column1") 9
              , Tuple (Tuple "row1" "column2") 9
              , Tuple (Tuple "row2" "column1") 1
              , Tuple (Tuple "row2" "column2") 1
              ]
            table = fromRightEx $ Table.mk mk mk (Map.fromFoldable cells)
        dominatesWeakly table "row1" "row3" `shouldEqual` Nothing
    describe "Strong" do
      it "returns `Just true` for domination" do
        let cells =
              [ Tuple (Tuple "row1" "column1") 9
              , Tuple (Tuple "row1" "column2") 9
              , Tuple (Tuple "row2" "column1") 1
              , Tuple (Tuple "row2" "column2") 1
              ]
            table = fromRightEx $ Table.mk mk mk (Map.fromFoldable cells)
        dominatesStrongly table "row1" "row2" `shouldEqual` Just true
      it "returns `Just false` for non-domination" do
        let cells =
              [ Tuple (Tuple "row1" "column1") 1
              , Tuple (Tuple "row1" "column2") 1
              , Tuple (Tuple "row2" "column1") 1
              , Tuple (Tuple "row2" "column2") 1
              ]
            table = fromRightEx $ Table.mk mk mk (Map.fromFoldable cells)
        dominatesStrongly table "row1" "row2" `shouldEqual` Just false
      it "returns `Nothing` for missing rows" do
        let cells =
              [ Tuple (Tuple "row1" "column1") 9
              , Tuple (Tuple "row1" "column2") 9
              , Tuple (Tuple "row2" "column1") 1
              , Tuple (Tuple "row2" "column2") 1
              ]
            table = fromRightEx $ Table.mk mk mk (Map.fromFoldable cells)
        dominatesStrongly table "row1" "row3" `shouldEqual` Nothing
