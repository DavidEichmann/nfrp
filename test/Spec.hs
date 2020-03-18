{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import qualified GHC.Generics as GHC
import Control.Monad (when)
import Data.Kind (Type)
import Data.Maybe (isJust, isNothing, fromMaybe)
import qualified System.Timeout as Sys
import Data.Text.Prettyprint.Doc
import Generics.SOP

-- import NFRP
-- import FRP
import Time
import TimeSpan
import KnowledgeBase
import KnowledgeBase.Timeline

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
    -- [ testCase "mtCropView" $ do
    --     -- mtFromList :: [a] -> MultiTimeline a
    --     let mt = mtFromList [FS_Point 1, FS_Span (spanExc 1 Nothing)]
    --     -- mtCropView :: CropView a FactSpan [a] [a] => MultiTimeline a -> FactSpan -> (MultiTimeline a, MultiTimeline a)
    --         (ins, outs) = mtCropView mt (FS_Point 1)
    --     unMultiTimeline ins  @?= [FS_Point 1]
    --     unMultiTimeline outs @?= [FS_Span (spanExc 1 Nothing)]
    -- ]

    testGroup "KnowledgeBase"
    [ testCase "Example Game" $ do
        let err = show kb
            kbInit = newKnowledgeBase gameLogic
            input1Facts = facts sourceEvent1 Nothing Nothing [ (1, "a"), (10, "b"), (100, "c")]
                       ++ facts sourceEvent2 Nothing Nothing [ (0, "A"), (10, "B"), (110, "C")]
            -- input1Facts = facts sourceEvent1 Nothing (Just 1) [  ]
            --            ++ facts sourceEvent1 (Just 1) Nothing [  ]
            kb = insertFacts input1Facts kbInit

        assertEqual err (Just Nothing)    (lookupE sourceEvent1 0   kb)
        assertEqual err (Just (Just "a")) (lookupE sourceEvent1 1   kb)
        assertEqual err (Just Nothing)    (lookupE sourceEvent1 5   kb)
        assertEqual err (Just (Just "b")) (lookupE sourceEvent1 10  kb)
        assertEqual err (Just Nothing)    (lookupE sourceEvent1 50  kb)
        assertEqual err (Just (Just "c")) (lookupE sourceEvent1 100 kb)
        assertEqual err (Just Nothing)    (lookupE sourceEvent1 101 kb)

        assertEqual err (Just Nothing)          (lookupE mappedEvent1 0   kb)
        assertEqual err (Just (Just "hello a")) (lookupE mappedEvent1 1   kb)
        assertEqual err (Just Nothing)          (lookupE mappedEvent1 2   kb)
        assertEqual err (Just Nothing)          (lookupE mappedEvent1 5   kb)
        assertEqual err (Just (Just "hello b")) (lookupE mappedEvent1 10  kb)
        assertEqual err (Just Nothing)          (lookupE mappedEvent1 20  kb)
        assertEqual err (Just Nothing)          (lookupE mappedEvent1 50  kb)
        assertEqual err (Just (Just "hello c")) (lookupE mappedEvent1 100 kb)
        assertEqual err (Just Nothing)          (lookupE mappedEvent1 110 kb)

        assertEqual err (Just Nothing)           (lookupE mappedEvent1x 0   kb)
        assertEqual err (Just (Just "xhello a")) (lookupE mappedEvent1x 1   kb)
        assertEqual err (Just Nothing)           (lookupE mappedEvent1x 2   kb)
        assertEqual err (Just Nothing)           (lookupE mappedEvent1x 5   kb)
        assertEqual err (Just (Just "xhello b")) (lookupE mappedEvent1x 10  kb)
        assertEqual err (Just Nothing)           (lookupE mappedEvent1x 20  kb)
        assertEqual err (Just Nothing)           (lookupE mappedEvent1x 50  kb)
        assertEqual err (Just (Just "xhello c")) (lookupE mappedEvent1x 100 kb)
        assertEqual err (Just Nothing)           (lookupE mappedEvent1x 110 kb)

        assertEqual err (Just Nothing)     (lookupE simultaneousEvent 0   kb)
        assertEqual err (Just Nothing)     (lookupE simultaneousEvent 1   kb)
        assertEqual err (Just Nothing)     (lookupE simultaneousEvent 5   kb)
        assertEqual err (Just (Just "bB")) (lookupE simultaneousEvent 10  kb)
        assertEqual err (Just Nothing)     (lookupE simultaneousEvent 50  kb)
        assertEqual err (Just Nothing)     (lookupE simultaneousEvent 100 kb)
        assertEqual err (Just Nothing)     (lookupE simultaneousEvent 110 kb)

        -- assertEqual err (Just "init") (lookupB steppedInput1 X_NegInf kb)
        -- assertEqual err (Just "init") (lookupB steppedInput1 0 kb)
        -- assertEqual err (Just "init") (lookupB steppedInput1 1 kb)
        -- assertEqual err (Just "a") (lookupB steppedInput1 (X_JustAfter 1) kb)
        -- assertEqual err (Just "a") (lookupB steppedInput1 2 kb)
        -- assertEqual err (Just "a") (lookupB steppedInput1 10 kb)
        -- assertEqual err (Just "b") (lookupB steppedInput1 (X_JustAfter 10) kb)
        -- assertEqual err (Just "b") (lookupB steppedInput1 50 kb)
        -- assertEqual err (Just "a") (lookupB steppedInput1 100 kb)
        -- assertEqual err (Just "c") (lookupB steppedInput1 (X_JustAfter 100) kb)
        -- assertEqual err (Just "c") (lookupB steppedInput1 150 kb)
        -- assertEqual err (Just "c") (lookupB steppedInput1 X_Inf kb)

        -- assertEqual err (Nothing) (lookupB steppedInput1 0 kb)
        -- assertEqual err (Just ()) (lookupB steppedInput1 1 kb)
        -- assertEqual err (Nothing) (lookupB steppedInput1 2 kb)
        -- assertEqual err (Just ()) (lookupB steppedInput1 5 kb)
        -- assertEqual err (Nothing) (lookupB steppedInput1 20 kb)
        -- assertEqual err (Just ()) (lookupB steppedInput1 50 kb)
        -- assertEqual err (Nothing) (lookupB steppedInput1 60 kb)
    ]
  ]

-- Describes all the data E/Bs of the game (and inputs)
data Game (f :: GameData) = Game
    { sourceEvent1        :: SE Game f String
    , sourceEvent2        :: SE Game f String
    , mappedEvent1        :: E Game f String
    , mappedEvent1x       :: E Game f String
    , simultaneousEvent   :: E Game f String
    -- , steppedInput1 :: B Game f String
    } deriving (GHC.Generic, Generic, FieldIx)

gameLogic :: Game 'Definition
gameLogic = Game
    { sourceEvent1 = sourceEventDef
    , sourceEvent2 = sourceEventDef

    -- Map source event.
    , mappedEvent1 = event $ do
        occ <- getE sourceEvent1
        return $ ("hello " ++) <$> occ

    -- Map a mapped event
    , mappedEvent1x = event $ do
        occ <- getE mappedEvent1
        return $ ("x" ++) <$> occ

    -- Combine multiple events.
    , simultaneousEvent = event $ do
        occA <- getE sourceEvent1
        occB <- getE sourceEvent2
        return $ (++) <$> occA <*> occB


    -- , steppedInput1 = foldB "init" $ do
    --     occ <- getE sourceEvent1
    --     -- oldVal <- getB steppedInput1
    --     -- return (fromMaybe oldVal occ)
    --     return (fromMaybe "xxx" occ)
    }

