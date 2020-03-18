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
            input1Facts = facts input1 Nothing Nothing [ (1, "a"), (10, "b"), (100, "c")]
            -- input1Facts = facts input1 Nothing (Just 1) [  ]
            --            ++ facts input1 (Just 1) Nothing [  ]
            kb = insertFacts input1Facts kbInit

        assertEqual err (Just Nothing)    (lookupE input1 0   kb)
        assertEqual err (Just (Just "a")) (lookupE input1 1   kb)
        assertEqual err (Just Nothing)    (lookupE input1 5   kb)
        assertEqual err (Just (Just "b")) (lookupE input1 10  kb)
        assertEqual err (Just Nothing)    (lookupE input1 50  kb)
        assertEqual err (Just (Just "c")) (lookupE input1 100 kb)
        assertEqual err (Just Nothing)    (lookupE input1 101 kb)


        assertEqual err (Just Nothing)          (lookupE mappedInput1 0   kb)
        assertEqual err (Just (Just "hello a")) (lookupE mappedInput1 1   kb)
        assertEqual err (Just Nothing)          (lookupE mappedInput1 2   kb)
        assertEqual err (Just Nothing)          (lookupE mappedInput1 5   kb)
        assertEqual err (Just (Just "hello b")) (lookupE mappedInput1 10  kb)
        assertEqual err (Just Nothing)          (lookupE mappedInput1 20  kb)
        assertEqual err (Just Nothing)          (lookupE mappedInput1 50  kb)
        assertEqual err (Just (Just "hello c")) (lookupE mappedInput1 100 kb)
        assertEqual err (Just Nothing)          (lookupE mappedInput1 110 kb)


        assertEqual err (Just Nothing)          (lookupE mappedInput1x 0   kb)
        assertEqual err (Just (Just "xhello a")) (lookupE mappedInput1x 1   kb)
        assertEqual err (Just Nothing)          (lookupE mappedInput1x 2   kb)
        assertEqual err (Just Nothing)          (lookupE mappedInput1x 5   kb)
        assertEqual err (Just (Just "xhello b")) (lookupE mappedInput1x 10  kb)
        assertEqual err (Just Nothing)          (lookupE mappedInput1x 20  kb)
        assertEqual err (Just Nothing)          (lookupE mappedInput1x 50  kb)
        assertEqual err (Just (Just "xhello c")) (lookupE mappedInput1x 100 kb)
        assertEqual err (Just Nothing)          (lookupE mappedInput1x 110 kb)

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
    { input1        :: SE Game f String
    , mappedInput1  :: E Game f String
    , mappedInput1x :: E Game f String
    -- , steppedInput1 :: B Game f String
    } deriving (GHC.Generic, Generic, FieldIx)

gameLogic :: Game 'Definition
gameLogic = Game
    { input1 = sourceEventDef

    , mappedInput1 = event $ do
        occ <- getE input1
        return $ ("hello " ++) <$> occ

    , mappedInput1x = event $ do
        occ <- getE mappedInput1
        return $ ("x" ++) <$> occ

    -- , steppedInput1 = foldB "init" $ do
    --     occ <- getE input1
    --     -- oldVal <- getB steppedInput1
    --     -- return (fromMaybe oldVal occ)
    --     return (fromMaybe "xxx" occ)
    }

