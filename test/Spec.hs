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
-- import Time
import TimeSpan
import Theory
-- import KnowledgeBase
-- import KnowledgeBase.Timeline

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "lcTransaction"
  [ testGroup "Model"
    [ testCase "GetE Only" $ do
        let
          eix1, eix2, eix3 :: EIx Int
          eix1 = EIx 1
          eix2 = EIx 2
          eix3 = EIx 3

          kb :: KnowledgeBase
          kb = solution1
                -- time: --0--------5-----7--------------
                --------------------------9______________
                [ InputEl eix1
                    (Left [ FactNoOcc [] (spanExc Nothing (Just 7))
                          , FactMayOcc [] 7 (Just 9)
                          ]
                    )
                -- time: --0--------5-----7--------------
                -------------------90____80______________
                , InputEl eix2
                    (Left [ FactNoOcc [] (spanExc Nothing (Just 5))
                          , FactMayOcc [] 5 (Just 90)
                          , FactMayOcc [] 7 (Just 80)
                          ]
                    )
                -- time: --0--------5-----7--------------
                ------------------190____189_____________
                , InputEl eix3
                    (Right $ do
                        e1 <- fromMaybe 0 <$> getE eix1
                        e2 <- fromMaybe 0 <$> getE eix2
                        return (e1+e2+100)
                    )
                ]

        -- lookupEKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
        lookupEKB 0 eix3 kb @?= Known Nothing
        lookupEKB 5 eix3 kb @?= Known (Just 190)
        lookupEKB 6 eix3 kb @?= Unknown
        lookupEKB 7 eix3 kb @?= Known (Just 189)
        lookupEKB 8 eix3 kb @?= Unknown

      , testCase "PrevE Only" $ do
        let
          eix1, eix2 :: EIx Int
          eix1 = EIx 1
          eix2 = EIx 2

          kb :: KnowledgeBase
          kb = solution1
                -- time: --0--------5-----7--------------
                -----------7--------8_____9______________
                [ InputEl eix1
                    (Left [ FactNoOcc [] (spanExc Nothing (Just 0))
                          , FactMayOcc [] 0 (Just 7)
                          , FactNoOcc [] (spanExc (Just 0) (Just 5))
                          , FactMayOcc [] 5 (Just 8)
                          , FactMayOcc [] 7 (Just 9)
                          ]
                    )
                -- time: --0--------5-----7--------------
                ---------100------107____________________
                , InputEl eix2
                    (Right $ do
                        _ <- requireE eix1
                        e1 <- fromMaybe 0 <$> prevE eix1
                        return (e1+100)
                    )
                ]

        -- lookupEKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
        lookupEKB (-1) eix2 kb @?= Known Nothing
        lookupEKB 0 eix2 kb @?= Known (Just 100)
        lookupEKB 2 eix2 kb @?= Known Nothing
        lookupEKB 5 eix2 kb @?= Known (Just 107)
        lookupEKB 6 eix2 kb @?= Unknown
        lookupEKB 7 eix2 kb @?= Unknown
        lookupEKB 8 eix2 kb @?= Unknown


      , testCase "GetE and PrevE (no self reference)" $ do
        let
          eix1, eix2, eix3 :: EIx Int
          eix1 = EIx 1
          eix2 = EIx 2
          eix3 = EIx 3

          kb :: KnowledgeBase
          kb = solution1
                -- time: --0--------5-----7-----9--------
                --------------------3-----1----__________
                [ InputEl eix1
                    (Left [ FactNoOcc [] (spanExc Nothing (Just 5))
                          , FactMayOcc [] 5 (Just 3)
                          , FactNoOcc [] (spanExc (Just 5) (Just 7))
                          , FactMayOcc [] 7 (Just 1)
                          , FactNoOcc [] (spanExc (Just 7) (Just 9))
                          ]
                    )
                -- time: --0--------5-----7-----9--------
                -------------------90____80____70________
                , InputEl eix2
                    (Left [ FactNoOcc [] (spanExc Nothing (Just 5))
                          , FactMayOcc [] 5 (Just 90)
                          , FactMayOcc [] 7 (Just 80)
                          , FactMayOcc [] 9 (Just 70)
                          ]
                    )
                -- time: --0--------5-----7-----9--------
                -------------------190___183___171_______
                , InputEl eix3
                    (Right $ do
                        e1 <- fromMaybe 0 <$> prevE eix1
                        e2 <- fromMaybe 0 <$> getE  eix2
                        return (e1+e2+100)
                    )
                ]

        -- lookupEKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
        lookupEKB 0 eix3 kb @?= Known Nothing
        lookupEKB 5 eix3 kb @?= Known (Just 190)
        lookupEKB 6 eix3 kb @?= Unknown
        lookupEKB 7 eix3 kb @?= Known (Just 183)
        lookupEKB 8 eix3 kb @?= Unknown
        lookupEKB 9 eix3 kb @?= Known (Just 171)


      , testCase "GetE and PrevE (with self reference after requireE)" $ do
        let
          eix1, eix2 :: EIx Int
          eix1 = EIx 1
          eix2 = EIx 2

          kb :: KnowledgeBase
          kb = solution1
                -- time: --0--------5-----7-----9--------
                --------------------3-----1_____5____
                [ InputEl eix1
                    (Left [ FactNoOcc [] (spanExc Nothing (Just 5))
                          , FactMayOcc [] 5 (Just 3)
                          , FactNoOcc [] (spanExc (Just 5) (Just 7))
                          , FactMayOcc [] 7 (Just 1)
                          , FactMayOcc [] 9 (Just 5)
                          ]
                    )
                -- time: --0--------5-----7-----9--------
                --------------------3-----4______________
                , InputEl eix2
                    (Right $ do
                        delta    <- requireE eix1
                        sumSoFar <- fromMaybe 0 <$> prevE eix2 -- Self reference
                        return (sumSoFar + delta)
                    )
                ]

        -- lookupEKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
        lookupEKB 0 eix2 kb @?= Known Nothing
        lookupEKB 5 eix2 kb @?= Known (Just 3)
        lookupEKB 6 eix2 kb @?= Known Nothing
        lookupEKB 7 eix2 kb @?= Known (Just 4)
        lookupEKB 8 eix2 kb @?= Unknown
        lookupEKB 9 eix2 kb @?= Unknown
        lookupEKB 10 eix2 kb @?= Unknown


      -- | This is the same as the last test, but the order of the GetE and
      -- PrevE swapped. This is significantly harder for the solver.
      , testCase "PrevE and GetE (with self reference before requireE)" $ do
        let
          eix1, eix2 :: EIx Int
          eix1 = EIx 1
          eix2 = EIx 2

          kb :: KnowledgeBase
          kb = solution1
                -- time: -----------5-----7-----111--------
                --------------------3-----1_____5____
                [ InputEl eix1
                    (Left [ FactNoOcc [] (spanExc Nothing (Just 5))
                          , FactMayOcc [] 5 (Just 3)
                          , FactNoOcc [] (spanExc (Just 5) (Just 7))
                          , FactMayOcc [] 7 (Just 1)
                          , FactMayOcc [] 111 (Just 5)
                          ]
                    )
                -- time: -----------5-----7-----111--------
                --------------------3-----4______________
                , InputEl eix2
                    (Right $ do
                        sumSoFar <- fromMaybe 0 <$> prevE eix2 -- Self reference
                        -- Require happens after self reference which disallows
                        -- short circuiting when eix1 is not occurring.
                        delta    <- requireE eix1
                        return (sumSoFar + delta)
                    )
                ]

        -- lookupEKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
        lookupEKB 0 eix2 kb @?= Known Nothing
        lookupEKB 5 eix2 kb @?= Known (Just 3)
        lookupEKB 6 eix2 kb @?= Known Nothing
        lookupEKB 7 eix2 kb @?= Known (Just 4)
        lookupEKB 8 eix2 kb @?= Unknown
        mapM_ (fail . ("\n" ++) . unlines . reverse) (maybeKnownToMaybe $ lookupEKBTrace 111 eix2 kb)
        lookupEKB 111 eix2 kb @?= Unknown         -- This is failing with actual value `Just (Just 9)` I think somwhere I've confused a prevE value of "Unknown" with "No previous occurence"
        lookupEKB 112 eix2 kb @?= Unknown


      , testCase "GetE and PrevE (with self reference after requireE and missing info)" $ do
        let
          eix1, eix2 :: EIx Int
          eix1 = EIx 1
          eix2 = EIx 2

          kb :: KnowledgeBase
          kb = solution1
                -- time: --0--------5-----7-----9--------
                -----------_--------3-----1_____5____
                [ InputEl eix1
                    (Left [ FactNoOcc [] (spanExc Nothing (Just 0))
                          -- Missing info at t=5
                          , FactNoOcc [] (spanExc (Just 0) (Just 5))
                          , FactMayOcc [] 5 (Just 3)
                          , FactNoOcc [] (spanExc (Just 5) (Just 7))
                          , FactMayOcc [] 7 (Just 1)
                          , FactMayOcc [] 9 (Just 5)
                          ]
                    )
                -- time: --0--------5-----7-----9--------
                -----------_--------_-----_______________
                -- Note that because of the use of `requireE`, exi2 is not a
                -- dependency at e.g. t∈{2,6} so we know that the event isn't
                -- occurring.
                , InputEl eix2
                    (Right $ do
                        delta    <- requireE eix1
                        sumSoFar <- fromMaybe 0 <$> prevE eix2 -- Self reference
                        return (sumSoFar + delta)
                    )
                ]

        -- lookupEKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
        lookupEKB (-1) eix2 kb @?= Known Nothing
        lookupEKB 0 eix2 kb @?= Unknown
        lookupEKB 1 eix2 kb @?= Known Nothing
        lookupEKB 5 eix2 kb @?= Unknown
        lookupEKB 6 eix2 kb @?= Known Nothing
        lookupEKB 7 eix2 kb @?= Unknown
        lookupEKB 8 eix2 kb @?= Unknown
        lookupEKB 9 eix2 kb @?= Unknown
        lookupEKB 10 eix2 kb @?= Unknown
    ]
  ]


-- tests :: TestTree
-- tests = testGroup "lcTransaction"
--   [ {- testGroup "TimeD"
--     [ testProperty "DI_Exactly t < DI_JustAfter t"
--       (\ t -> DI_Exactly t < DI_JustAfter t)
--     , testProperty "DI_Exactly t < DI_Inf"
--       (\ t -> DI_Exactly t < DI_Inf)
--     , testProperty "DI_JustAfter t < DI_Inf"
--       (\ t -> DI_JustAfter t < DI_Inf)
--     , testProperty "DI_JustAfter t == delay (DI_JustAfter t)"
--       (\ t -> DI_JustAfter t == delay (DI_JustAfter t))
--     ]
--   , testGroup "SpanIncExc"
--     [ testProperty "spanIncExc"
--         (\ loMay hiMay ->  let s = spanIncExc loMay hiMay in case (loMay, hiMay) of
--               (Just lo, Just hi) -> lo < hi ==> s == s
--               _ -> property (s == s)
--         )
--     , testProperty "LeftSpaceExc intersect with allT LeftSpaceExc is self"
--         (\ (l :: LeftSpaceExc) -> (All :: AllOr LeftSpaceExc) `intersect` l == l)
--     , testProperty "RightSpaceExc intersect with allT RightSpaceExc is self"
--         (\ (l :: RightSpaceExc) -> (All :: AllOr RightSpaceExc) `intersect` l == l)
--     , testProperty "span intersect self is self"
--         (\ (s :: SpanIncExc) -> s `intersect` s == Just s)
--     , testProperty "span diff span -> all endsOn eachother"
--         (\ (s1 :: SpanIncExc) (s2 :: SpanIncExc) -> case s1 `difference` s2 of
--             (Just l, Just r) -> property (isJust (l `endsOn` s2) && isJust (s2 `endsOn` r))
--             _ -> property Discard
--         )
--     ]
--   , -}
--     -- [ testCase "mtCropView" $ do
--     --     -- mtFromList :: [a] -> MultiTimeline a
--     --     let mt = mtFromList [FS_Point 1, FS_Span (spanExc 1 Nothing)]
--     --     -- mtCropView :: CropView a FactSpan [a] [a] => MultiTimeline a -> FactSpan -> (MultiTimeline a, MultiTimeline a)
--     --         (ins, outs) = mtCropView mt (FS_Point 1)
--     --     unMultiTimeline ins  @?= [FS_Point 1]
--     --     unMultiTimeline outs @?= [FS_Span (spanExc 1 Nothing)]
--     -- ]

--     testGroup "KnowledgeBase"
--     [ testCase "Example Game" $ do
--         let err = show kb
--             kbInit = newKnowledgeBase gameLogic
--             input1Facts = facts sourceEvent1 Nothing Nothing [ (1, "a"), (10, "b"), (100, "c")]
--                        ++ facts sourceEvent2 Nothing Nothing [ (0, "A"), (10, "B"), (110, "C")]
--             -- input1Facts = facts sourceEvent1 Nothing (Just 0) []
--             --            ++ facts sourceEvent1 (Just 0) (Just 10) []
--             kb = insertFacts input1Facts kbInit

--         -- assertEqual err (Just Nothing)    (lookupE sourceEvent1 0   kb)
--         -- assertEqual err (Just (Just "a")) (lookupE sourceEvent1 1   kb)
--         -- assertEqual err (Just Nothing)    (lookupE sourceEvent1 5   kb)
--         -- assertEqual err (Just (Just "b")) (lookupE sourceEvent1 10  kb)
--         -- assertEqual err (Just Nothing)    (lookupE sourceEvent1 50  kb)
--         -- assertEqual err (Just (Just "c")) (lookupE sourceEvent1 100 kb)
--         -- assertEqual err (Just Nothing)    (lookupE sourceEvent1 101 kb)

--         -- assertEqual err (Just Nothing)          (lookupE mappedEvent1 0   kb)
--         -- assertEqual err (Just (Just "hello a")) (lookupE mappedEvent1 1   kb)
--         -- assertEqual err (Just Nothing)          (lookupE mappedEvent1 2   kb)
--         -- assertEqual err (Just Nothing)          (lookupE mappedEvent1 5   kb)
--         -- assertEqual err (Just (Just "hello b")) (lookupE mappedEvent1 10  kb)
--         -- assertEqual err (Just Nothing)          (lookupE mappedEvent1 20  kb)
--         -- assertEqual err (Just Nothing)          (lookupE mappedEvent1 50  kb)
--         -- assertEqual err (Just (Just "hello c")) (lookupE mappedEvent1 100 kb)
--         -- assertEqual err (Just Nothing)          (lookupE mappedEvent1 110 kb)

--         -- assertEqual err (Just Nothing)           (lookupE mappedEvent1x 0   kb)
--         -- assertEqual err (Just (Just "xhello a")) (lookupE mappedEvent1x 1   kb)
--         -- assertEqual err (Just Nothing)           (lookupE mappedEvent1x 2   kb)
--         -- assertEqual err (Just Nothing)           (lookupE mappedEvent1x 5   kb)
--         -- assertEqual err (Just (Just "xhello b")) (lookupE mappedEvent1x 10  kb)
--         -- assertEqual err (Just Nothing)           (lookupE mappedEvent1x 20  kb)
--         -- assertEqual err (Just Nothing)           (lookupE mappedEvent1x 50  kb)
--         -- assertEqual err (Just (Just "xhello c")) (lookupE mappedEvent1x 100 kb)
--         -- assertEqual err (Just Nothing)           (lookupE mappedEvent1x 110 kb)

--         -- assertEqual err (Just Nothing)     (lookupE simultaneousEvent 0   kb)
--         -- assertEqual err (Just Nothing)     (lookupE simultaneousEvent 1   kb)
--         -- assertEqual err (Just Nothing)     (lookupE simultaneousEvent 5   kb)
--         -- assertEqual err (Just (Just "bB")) (lookupE simultaneousEvent 10  kb)
--         -- assertEqual err (Just Nothing)     (lookupE simultaneousEvent 50  kb)
--         -- assertEqual err (Just Nothing)     (lookupE simultaneousEvent 100 kb)
--         -- assertEqual err (Just Nothing)     (lookupE simultaneousEvent 110 kb)

--         assertEqual err (Just "init") (lookupB steppedSE1 X_NegInf kb)
--         assertEqual err (Just "init") (lookupB steppedSE1 0 kb)
--         assertEqual err (Just "init") (lookupB steppedSE1 1 kb)
--         assertEqual err (Just "a")    (lookupB steppedSE1 (X_JustAfter 1) kb)
--         assertEqual err (Just "a")    (lookupB steppedSE1 2 kb)
--         assertEqual err (Just "a")    (lookupB steppedSE1 10 kb)
--         assertEqual err (Just "b")    (lookupB steppedSE1 (X_JustAfter 10) kb)
--         assertEqual err (Just "b")    (lookupB steppedSE1 50 kb)
--         assertEqual err (Just "b")    (lookupB steppedSE1 100 kb)
--         assertEqual err (Just "c")    (lookupB steppedSE1 (X_JustAfter 100) kb)
--         assertEqual err (Just "c")    (lookupB steppedSE1 150 kb)
--         assertEqual err (Just "c")    (lookupB steppedSE1 X_Inf kb)

--         assertEqual err (Just "init") (lookupB steppedSimultaneousEvent X_NegInf kb)
--         assertEqual err (Just "init") (lookupB steppedSimultaneousEvent 0 kb)
--         assertEqual err (Just "init") (lookupB steppedSimultaneousEvent 1 kb)
--         assertEqual err (Just "init") (lookupB steppedSimultaneousEvent (X_JustAfter 1) kb)
--         assertEqual err (Just "init") (lookupB steppedSimultaneousEvent 2 kb)
--         assertEqual err (Just "init") (lookupB steppedSimultaneousEvent 10 kb)
--         assertEqual err (Just "bB") (lookupB steppedSimultaneousEvent (X_JustAfter 10) kb)
--         assertEqual err (Just "bB") (lookupB steppedSimultaneousEvent 50 kb)
--         assertEqual err (Just "bB") (lookupB steppedSimultaneousEvent 100 kb)
--         assertEqual err (Just "bB") (lookupB steppedSimultaneousEvent (X_JustAfter 100) kb)
--         assertEqual err (Just "bB") (lookupB steppedSimultaneousEvent 150 kb)
--         assertEqual err (Just "bB") (lookupB steppedSimultaneousEvent X_Inf kb)
--     ]
--   ]

-- -- Describes all the data E/Bs of the game (and inputs)
-- data Game (f :: GameData) = Game
--     { sourceEvent1                :: SE Game f String
--     , sourceEvent2                :: SE Game f String
--     , mappedEvent1                :: E Game f String
--     , mappedEvent1x               :: E Game f String
--     , simultaneousEvent           :: E Game f String
--     , steppedSE1                  :: B Game f String
--     , steppedSimultaneousEvent    :: B Game f String
--     } deriving (GHC.Generic, Generic, FieldIx)

-- gameLogic :: Game 'Definition
-- gameLogic = Game
--     { sourceEvent1 = sourceEventDef
--     , sourceEvent2 = sourceEventDef

--     -- Map source event.
--     , mappedEvent1 = event $ do
--         occ <- getE sourceEvent1
--         return $ ("hello " ++) <$> occ

--     -- Map a mapped event
--     , mappedEvent1x = event $ do
--         occ <- getE mappedEvent1
--         return $ ("x" ++) <$> occ

--     -- Combine multiple events.
--     , simultaneousEvent = event $ do
--         occA <- getE sourceEvent1
--         occB <- getE sourceEvent2
--         return $ (++) <$> occA <*> occB

--       -- TODO How do we implement step correctly? We should support both:
--       --   * refer to previous value of this behavior (getB steppedSE1). I think
--       --     this is currently broken
--       --     * maybe `foldB` should always be given the previous value
--       --       (implemented with getB)? And cases that don't want the previous
--       --       value should use `step` or `behavior`
--       --   * Allow this rule to return MaybeChange.
--     , steppedSE1 = foldB "init" $ do
--         occ <- getE sourceEvent1
--         oldVal <- getB steppedSE1
--         return (fromMaybe oldVal occ)

--     -- , steppedSE1' = step "init" $ do
--     --     occ <- getE sourceEvent1
--     --     return occ

--     , steppedSimultaneousEvent = foldB "init" $ do
--         occ <- getE simultaneousEvent
--         oldVal <- getB steppedSimultaneousEvent
--         return (fromMaybe oldVal occ)

--     -- , steppedSimultaneousEvent' = step "init" $ do
--     --     occ <- getE simultaneousEvent
--     --     return occ
--     }

