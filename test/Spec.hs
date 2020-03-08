{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE KindSignatures #-}

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Control.Monad (when)
import Data.Kind (Type)
import Data.Maybe (isJust, isNothing, fromMaybe)
import qualified System.Timeout as Sys

import NFRP
import FRP
import Time
import TimeSpan
import KnowledgeBase

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "lcTransaction"
  [ {- testGroup "TimeD"
    [ testProperty "DI_Exactly t < DI_JustAfter t"
      (\ t -> DI_Exactly t < DI_JustAfter t)
    , testProperty "DI_Exactly t < DI_Inf"
      (\ t -> DI_Exactly t < DI_Inf)
    , testProperty "DI_JustAfter t < DI_Inf"
      (\ t -> DI_JustAfter t < DI_Inf)
    , testProperty "DI_JustAfter t == delay (DI_JustAfter t)"
      (\ t -> DI_JustAfter t == delay (DI_JustAfter t))
    ]
  , testGroup "SpanIncExc"
    [ testProperty "spanIncExc"
        (\ loMay hiMay ->  let s = spanIncExc loMay hiMay in case (loMay, hiMay) of
              (Just lo, Just hi) -> lo < hi ==> s == s
              _ -> property (s == s)
        )
    , testProperty "LeftSpaceExc intersect with allT LeftSpaceExc is self"
        (\ (l :: LeftSpaceExc) -> (All :: AllOr LeftSpaceExc) `intersect` l == l)
    , testProperty "RightSpaceExc intersect with allT RightSpaceExc is self"
        (\ (l :: RightSpaceExc) -> (All :: AllOr RightSpaceExc) `intersect` l == l)
    , testProperty "span intersect self is self"
        (\ (s :: SpanIncExc) -> s `intersect` s == Just s)
    , testProperty "span diff span -> all endsOn eachother"
        (\ (s1 :: SpanIncExc) (s2 :: SpanIncExc) -> case s1 `difference` s2 of
            (Just l, Just r) -> property (isJust (l `endsOn` s2) && isJust (s2 `endsOn` r))
            _ -> property Discard
        )
    ]
  , -}
    testGroup "KnowledgeBase"
    [ testCase "Example Game" $ do
        let kbInit = newKnowledgeBase gameLogic
            input1Facts = facts input1 Nothing Nothing [ (1, "a"), (10, "b"), (100, "c")]
            -- player1InputBFacts = facts player1InputB Nothing Nothing [ (1, ()), (5, ()), (50, ())]
            kb = insertFacts input1Facts kbInit

        lookupE input1 0 kb   @?= Just (Nothing)
        lookupE input1 1 kb   @?= Just (Just "a")
        lookupE input1 5 kb   @?= Just (Nothing)
        lookupE input1 10 kb  @?= Just (Just "b")
        lookupE input1 50 kb  @?= Just (Nothing)
        lookupE input1 100 kb @?= Just (Just "c")
        lookupE input1 101 kb @?= Just (Nothing)

        -- lookupE input2 0 kb @?= Nothing
        -- lookupE input2 1 kb @?= Just ()
        -- lookupE input2 2 kb @?= Nothing
        -- lookupE input2 5 kb @?= Just ()
        -- lookupE input2 20 kb @?= Nothing
        -- lookupE input2 50 kb @?= Just ()
        -- lookupE input2 60 kb @?= Nothing

        -- lookupB steppedInput1 0 kb @?= Nothing
        -- lookupB steppedInput1 1 kb @?= Just ()
        -- lookupB steppedInput1 2 kb @?= Nothing
        -- lookupB steppedInput1 5 kb @?= Just ()
        -- lookupB steppedInput1 20 kb @?= Nothing
        -- lookupB steppedInput1 50 kb @?= Just ()
        -- lookupB steppedInput1 60 kb @?= Nothing
    ]
  ]

-- Describes all the data E/Bs of the game (and inputs)
data Game sourceEvent (event :: Type -> Type) behavior = Game
    { input1 :: sourceEvent String
    , steppedInput1 :: behavior String
    }

gameLogic :: GameDefinition Game
gameLogic = Game
    { input1 = SourceEvent
    , steppedInput1 = foldB "init" $ do
        occ <- getE input1
        return $ fromMaybe "init" occ
    }

-- TODO use generics to do this. Why do this like this? Well we'll need to send
-- facts over the network eventually, and we'll need a way to index those facts
-- on their corresponding field, so something like this seems inherently
-- necessary.
instance FieldIx Game where
    fieldIxs = Game
        { input1         = EIx 0
        , steppedInput1  = BIx 1
        }

    allGameBs =
        [ SomeKeyB steppedInput1
        ]
    allGameEs = []
    allGameSEs =
        [ SomeKeySE input1
        ]

