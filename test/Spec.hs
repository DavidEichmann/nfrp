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
import Time (Time)
import TimeSpan
import Theory
-- import KnowledgeBase
-- import KnowledgeBase.Timeline

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "lcTransaction"
  [ testGroup "Model - Event"
    [ testCase "GetV Only" $ do
        let
          eix1, eix2, eix3 :: VIx (MaybeOcc Int)
          eix1 = VIx 1
          eix2 = VIx 2
          eix3 = VIx 3

          kb :: KnowledgeBase
          kb = solution1
                -- time: --0--------5-----7--------------
                --------------------------9______________
                [ InputEl eix1
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 7)) Nothing
                          , Fact_Point   [] 7 (Just 9)
                          ]
                    )
                -- time: --0--------5-----7--------------
                -------------------90____80______________
                , InputEl eix2
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 5)) Nothing
                          , Fact_Point   [] 5 (Just 90)
                          , Fact_Point   [] 7 (Just 80)
                          ]
                    )
                -- time: --0--------5-----7--------------
                ------------------190____189_____________
                , InputEl eix3
                    (Right $ do
                        e1 <- getV eix1
                        e2 <- getV eix2
                        return $ case (e1, e2) of
                            (Nothing, Nothing) -> Nothing
                            _ -> Just $ 100
                                        + fromMaybe 0 e1
                                        + fromMaybe 0 e2
                    )
                ]

        -- lookupVKB :: Time -> VIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
        lookupVKB 0 eix3 kb @?= Known Nothing
        lookupVKB 5 eix3 kb @?= Known (Just 190)
        lookupVKB 6 eix3 kb @?= Unknown
        lookupVKB 7 eix3 kb @?= Known (Just 189)
        lookupVKB 8 eix3 kb @?= Unknown

      , testCase "PrevV Only" $ do
        let
          eix1, eix2 :: VIx (MaybeOcc Int)
          eix1 = VIx 1
          eix2 = VIx 2

          kb :: KnowledgeBase
          kb = solution1
                -- time: --0--------5-----7--------------
                -----------7--------8_____9______________
                [ InputEl eix1
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 0)) Nothing
                          , Fact_Point   [] 0 (Just 7)
                          , Fact_SpanExc [] (spanExc (Just 0) (Just 5)) Nothing
                          , Fact_Point   [] 5 (Just 8)
                          , Fact_Point   [] 7 (Just 9)
                          ]
                    )
                -- time: --0--------5-----7--------------
                ---------100------107____________________
                , InputEl eix2
                    (Right $ do
                        requireE eix1 $ \_ -> do
                            e1 <- prevE 0 eix1
                            return (e1+100)
                    )
                ]

        -- lookupVKB :: Time -> VIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
        lookupVKB (-1) eix2 kb @?= Known Nothing
        lookupVKB 0 eix2 kb @?= Known (Just 100)
        lookupVKB 2 eix2 kb @?= Known Nothing
        lookupVKB 5 eix2 kb @?= Known (Just 107)
        lookupVKB 6 eix2 kb @?= Unknown
        lookupVKB 7 eix2 kb @?= Unknown
        lookupVKB 8 eix2 kb @?= Unknown


      , testCase "GetV and PrevV (no self reference)" $ do
        let
          eix1, eix2, eix3 :: VIx (MaybeOcc Int)
          eix1 = VIx 1
          eix2 = VIx 2
          eix3 = VIx 3

          kb :: KnowledgeBase
          kb = solution1
                -- time: --0--------5-----7-----9--------
                --------------------3-----1----__________
                [ InputEl eix1
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 5)) Nothing
                          , Fact_Point   [] 5 (Just 3)
                          , Fact_SpanExc [] (spanExc (Just 5) (Just 7)) Nothing
                          , Fact_Point   [] 7 (Just 1)
                          , Fact_SpanExc [] (spanExc (Just 7) (Just 9)) Nothing
                          ]
                    )
                -- time: --0--------5-----7-----9--------
                -------------------90____80____70________
                , InputEl eix2
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 5)) Nothing
                          , Fact_Point   [] 5 (Just 90)
                          , Fact_Point   [] 7 (Just 80)
                          , Fact_Point   [] 9 (Just 70)
                          ]
                    )
                -- time: --0--------5-----7-----9--------
                -------------------190___183___171_______
                , InputEl eix3
                    (Right $ do
                        e1 <- prevE 0 eix1
                        e2May <- getV eix2
                        return $ case e2May of
                            Nothing -> Nothing
                            Just e2 -> Just (e1+e2+100)
                    )
                ]

        -- lookupVKB :: Time -> VIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
        lookupVKB 0 eix3 kb @?= Known Nothing
        lookupVKB 5 eix3 kb @?= Known (Just 190)
        lookupVKB 6 eix3 kb @?= Unknown
        lookupVKB 7 eix3 kb @?= Known (Just 183)
        lookupVKB 8 eix3 kb @?= Unknown
        lookupVKB 9 eix3 kb @?= Known (Just 171)


      , testCase "GetV and PrevV (with self reference after requireE)" $ do
        let
          eix1, eix2 :: VIx (MaybeOcc Int)
          eix1 = VIx 1
          eix2 = VIx 2

          kb :: KnowledgeBase
          kb = solution1
                -- time: --0--------5-----7-----9--------
                --------------------3-----1_____5____
                [ InputEl eix1
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 5)) Nothing
                          , Fact_Point   [] 5 (Just 3)
                          , Fact_SpanExc [] (spanExc (Just 5) (Just 7)) Nothing
                          , Fact_Point   [] 7 (Just 1)
                          , Fact_Point   [] 9 (Just 5)
                          ]
                    )
                -- time: --0--------5-----7-----9--------
                --------------------3-----4______________
                , InputEl eix2
                    (Right $ do
                        requireE eix1 $ \delta -> do
                            sumSoFar <- prevE 0 eix2 -- Self reference
                            return (sumSoFar + delta)
                    )
                ]

        -- lookupVKB :: Time -> VIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
        lookupVKB 0 eix2 kb @?= Known Nothing
        lookupVKB 5 eix2 kb @?= Known (Just 3)
        lookupVKB 6 eix2 kb @?= Known Nothing
        lookupVKB 7 eix2 kb @?= Known (Just 4)
        lookupVKB 8 eix2 kb @?= Unknown
        lookupVKB 9 eix2 kb @?= Unknown
        lookupVKB 10 eix2 kb @?= Unknown


      -- | This is the same as the last test, but the order of the GetV and
      -- PrevV swapped. This is significantly harder for the solver.
      , testCase "PrevV and GetV (with self reference before requireE)" $ do
        let
          eix1, eix2 :: VIx (MaybeOcc Int)
          eix1 = VIx 1
          eix2 = VIx 2

          kb :: KnowledgeBase
          kb = solution1
                -- time: -----------5-----7-----111--------
                --------------------3-----1_____5____
                [ InputEl eix1
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 5)) Nothing
                          , Fact_Point   [] 5 (Just 3)
                          , Fact_SpanExc [] (spanExc (Just 5) (Just 7)) Nothing
                          , Fact_Point   [] 7 (Just 1)
                          , Fact_Point   [] 111 (Just 5)
                          ]
                    )
                -- time: -----------5-----7-----111--------
                --------------------3-----4______________
                , InputEl eix2
                    (Right $ do
                        sumSoFar <- prevE 0 eix2 -- Self reference
                        -- Require happens after self reference which disallows
                        -- short circuiting when eix1 is not occurring.
                        requireE eix1 $ \delta ->
                            return (sumSoFar + delta)
                    )
                ]

        -- lookupVKB :: Time -> VIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
        lookupVKB 0 eix2 kb @?= Known Nothing
        lookupVKB 5 eix2 kb @?= Known (Just 3)
        lookupVKB 6 eix2 kb @?= Known Nothing
        lookupVKB 7 eix2 kb @?= Known (Just 4)
        lookupVKB 8 eix2 kb @?= Unknown
        lookupVKB 111 eix2 kb @?= Unknown
        lookupVKB 112 eix2 kb @?= Unknown


      , testCase "GetV and PrevV (with self reference after requireE and missing info)" $ do
        let
          eix1, eix2 :: VIx (MaybeOcc Int)
          eix1 = VIx 1
          eix2 = VIx 2

          kb :: KnowledgeBase
          kb = solution1
                -- time: --0--------5-----7-----9--------
                -----------_--------3-----1_____5____
                [ InputEl eix1
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 0)) Nothing
                          , Fact_SpanExc [] (spanExc (Just 0) (Just 5)) Nothing
                          , Fact_Point   [] 5 (Just 3)
                          , Fact_SpanExc [] (spanExc (Just 5) (Just 7)) Nothing
                          , Fact_Point   [] 7 (Just 1)
                          , Fact_Point   [] 9 (Just 5)
                          ]
                    )
                -- time: --0--------5-----7-----9--------
                -----------_--------_-----_______________
                -- Note that because of the use of `requireE`, exi2 is not a
                -- dependency at e.g. t∈{2,6} so we know that the event isn't
                -- occurring.
                , InputEl eix2
                    (Right $ do
                        requireE eix1 $ \delta -> do
                            sumSoFar <- prevE 0 eix2 -- Self reference
                            return (sumSoFar + delta)
                    )
                ]

        -- lookupVKB :: Time -> VIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
        lookupVKB (-1) eix2 kb @?= Known Nothing
        lookupVKB 0 eix2 kb @?= Unknown
        lookupVKB 1 eix2 kb @?= Known Nothing
        lookupVKB 5 eix2 kb @?= Unknown
        lookupVKB 6 eix2 kb @?= Known Nothing
        lookupVKB 7 eix2 kb @?= Unknown
        lookupVKB 8 eix2 kb @?= Unknown
        lookupVKB 9 eix2 kb @?= Unknown
        lookupVKB 10 eix2 kb @?= Unknown

    , testCase "Swap values (transitive self reference)" $ do
        let
          swapE :: VIx (MaybeOcc ())
          swapE = VIx 1

          a, b :: VIx (MaybeOcc String)
          a = VIx 2
          b = VIx 3

          kb :: KnowledgeBase
          kb = solution1
                -- time: --0--------5-----7-----9--------
                --------------------()----()____()_______
                [ InputEl swapE
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 5)) Nothing
                          , Fact_Point   [] 5 (Just ())
                          , Fact_SpanExc [] (spanExc (Just 5) (Just 7)) Nothing
                          , Fact_Point   [] 7 (Just ())
                          , Fact_Point   [] 9 (Just ())
                          ]
                    )
                -- time: --0--------5-----7-----9--------
                --------------------y-----x_______________
                , InputEl a
                    (Right $ do
                        requireE swapE $ \() -> do
                            bVal <- prevE "y" b
                            return bVal
                    )
                -- time: --0--------5-----7-----9--------
                --------------------x-----y_______________
                , InputEl b
                    (Right $ do
                        requireE swapE $ \() -> do
                            aVal <- prevE "x" a
                            return aVal
                    )
                ]

        lookupVKB 0  a kb @?= Known Nothing
        lookupVKB 0  b kb @?= Known Nothing
        lookupVKB 1  a kb @?= Known Nothing
        lookupVKB 1  b kb @?= Known Nothing
        lookupVKB 5  a kb @?= Known (Just "y")
        lookupVKB 5  b kb @?= Known (Just "x")
        lookupVKB 6  a kb @?= Known Nothing
        lookupVKB 6  b kb @?= Known Nothing
        lookupVKB 7  a kb @?= Known (Just "x")
        lookupVKB 7  b kb @?= Known (Just "y")
        lookupVKB 8  a kb @?= Unknown
        lookupVKB 8  b kb @?= Unknown
        lookupVKB 9  a kb @?= Unknown
        lookupVKB 9  b kb @?= Unknown
        lookupVKB 10 a kb @?= Unknown
        lookupVKB 10 b kb @?= Unknown


    , testCase "Switching" $ do
        let
          a, b, c :: VIx (MaybeOcc Int)
          a      = VIx 1
          b      = VIx 2
          c      = VIx 3

          switch :: VIx (MaybeOcc Int)
          switch = VIx 4

          out :: VIx (MaybeOcc Int)
          out    = VIx 5

          kb :: KnowledgeBase
          kb = solution1
                -- time: --0--2--4--6--8--10-12-14-16---
                -----------11-12-13-14-15-16-17-18-19---
                [ InputEl a
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 0)) Nothing
                          , Fact_Point [] 0 (Just 11)
                          , Fact_SpanExc [] (spanExc (Just 0) (Just 2)) Nothing
                          , Fact_Point [] 2 (Just 12)
                          , Fact_SpanExc [] (spanExc (Just 0) (Just 4)) Nothing
                          , Fact_Point [] 4 (Just 13)
                          , Fact_SpanExc [] (spanExc (Just 4) (Just 6)) Nothing
                          , Fact_Point [] 6 (Just 14)
                          , Fact_SpanExc [] (spanExc (Just 6) (Just 8)) Nothing
                          , Fact_Point [] 8 (Just 15)
                          , Fact_SpanExc [] (spanExc (Just 8) (Just 10)) Nothing
                          , Fact_Point [] 10 (Just 16)
                          , Fact_SpanExc [] (spanExc (Just 10) (Just 12)) Nothing
                          , Fact_Point [] 12 (Just 17)
                          , Fact_SpanExc [] (spanExc (Just 12) (Just 14)) Nothing
                          , Fact_Point [] 14 (Just 18)
                          , Fact_SpanExc [] (spanExc (Just 14) (Just 16)) Nothing
                          , Fact_Point [] 16 (Just 19)
                          , Fact_SpanExc [] (spanExc (Just 16) Nothing) Nothing
                          ]
                    )
                -- time: --0--2--4--6--8--10-12-14-16---
                -----------21-22-23-24-25-26-27-28-29---
                ,  InputEl b
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 0)) Nothing
                          , Fact_Point [] 0 (Just 21)
                          , Fact_SpanExc [] (spanExc (Just 0) (Just 2)) Nothing
                          , Fact_Point [] 2 (Just 22)
                          , Fact_SpanExc [] (spanExc (Just 0) (Just 4)) Nothing
                          , Fact_Point [] 4 (Just 23)
                          , Fact_SpanExc [] (spanExc (Just 4) (Just 6)) Nothing
                          , Fact_Point [] 6 (Just 24)
                          , Fact_SpanExc [] (spanExc (Just 6) (Just 8)) Nothing
                          , Fact_Point [] 8 (Just 25)
                          , Fact_SpanExc [] (spanExc (Just 8) (Just 10)) Nothing
                          , Fact_Point [] 10 (Just 26)
                          , Fact_SpanExc [] (spanExc (Just 10) (Just 12)) Nothing
                          , Fact_Point [] 12 (Just 27)
                          , Fact_SpanExc [] (spanExc (Just 12) (Just 14)) Nothing
                          , Fact_Point [] 14 (Just 28)
                          , Fact_SpanExc [] (spanExc (Just 14) (Just 16)) Nothing
                          , Fact_Point [] 16 (Just 29)
                          , Fact_SpanExc [] (spanExc (Just 16) Nothing) Nothing
                          ]
                    )
                -- time: --0--2--4--6--8--10-12-14-16---
                -----------31-32-33-34-35-36-37-38-39---
                ,  InputEl c
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 0)) Nothing
                          , Fact_Point [] 0 (Just 31)
                          , Fact_SpanExc [] (spanExc (Just 0) (Just 2)) Nothing
                          , Fact_Point [] 2 (Just 32)
                          , Fact_SpanExc [] (spanExc (Just 0) (Just 4)) Nothing
                          , Fact_Point [] 4 (Just 33)
                          , Fact_SpanExc [] (spanExc (Just 4) (Just 6)) Nothing
                          , Fact_Point [] 6 (Just 34)
                          , Fact_SpanExc [] (spanExc (Just 6) (Just 8)) Nothing
                          , Fact_Point [] 8 (Just 35)
                          , Fact_SpanExc [] (spanExc (Just 8) (Just 10)) Nothing
                          , Fact_Point [] 10 (Just 36)
                          , Fact_SpanExc [] (spanExc (Just 10) (Just 12)) Nothing
                          , Fact_Point [] 12 (Just 37)
                          , Fact_SpanExc [] (spanExc (Just 12) (Just 14)) Nothing
                          , Fact_Point [] 14 (Just 38)
                          , Fact_SpanExc [] (spanExc (Just 14) (Just 16)) Nothing
                          , Fact_Point [] 16 (Just 39)
                          , Fact_SpanExc [] (spanExc (Just 16) Nothing) Nothing
                          ]
                    )
                -- time: --0--2--4--6--8--10-12-14-16---
                -- (1) -------2-----3------1--_--2------
                ,  InputEl switch
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 0)) Nothing
                          , Fact_Point [] 0 Nothing
                          , Fact_SpanExc [] (spanExc (Just 0) (Just 2)) Nothing
                          , Fact_Point [] 2 (Just 2)
                          , Fact_SpanExc [] (spanExc (Just 2) (Just 6)) Nothing
                          , Fact_Point [] 6 (Just 3)
                          , Fact_SpanExc [] (spanExc (Just 6) (Just 10)) Nothing
                          , Fact_Point [] 10 (Just 1)
                          , Fact_SpanExc [] (spanExc (Just 10) (Just 12)) Nothing
                          -- Unknown at t=12
                          , Fact_SpanExc [] (spanExc (Just 12) (Just 14)) Nothing
                          , Fact_Point [] 14 (Just 2)
                          , Fact_SpanExc [] (spanExc (Just 14) Nothing) Nothing
                          ]
                    )
                -- time: --0--2--4--6--8--10-12---14-16---
                -----------11-12-23-24-35-36-17_____------
                , InputEl out
                    (Right $ do
                        switchVal <- prevE 1 switch
                        getV $ case switchVal of
                                1 -> a
                                2 -> b
                                3 -> c
                                x -> error $ "Unexpected switch value of: " ++ show x
                    )
                ]

        lookupVKB (-1) out kb @?= Known Nothing
        lookupVKB 0  out kb @?= Known (Just 11)
        lookupVKB 1  out kb @?= Known Nothing
        lookupVKB 2  out kb @?= Known (Just 12)
        lookupVKB 3  out kb @?= Known Nothing
        lookupVKB 4  out kb @?= Known (Just 23)
        lookupVKB 5  out kb @?= Known Nothing
        lookupVKB 6  out kb @?= Known (Just 24)
        lookupVKB 7  out kb @?= Known Nothing
        lookupVKB 8  out kb @?= Known (Just 35)
        lookupVKB 9  out kb @?= Known Nothing
        lookupVKB 10 out kb @?= Known (Just 36)
        lookupVKB 11 out kb @?= Known Nothing
        lookupVKB 12 out kb @?= Known (Just 17)
        lookupVKB 13 out kb @?= Unknown
        lookupVKB 14 out kb @?= Unknown
        lookupVKB 15 out kb @?= Known Nothing
        lookupVKB 16 out kb @?= Known (Just 29)
        lookupVKB 17 out kb @?= Known Nothing
    ]

  , testGroup "Model - Behavior"
    [ testCase "Switching" $ do
        let
          a, b, c :: VIx Int
          a      = VIx 1
          b      = VIx 2
          c      = VIx 3

          switch :: VIx (MaybeOcc Int)
          switch = VIx 4

          out :: VIx Int
          out    = VIx 5

          kb :: KnowledgeBase
          kb = solution1
                -- time:      0      10      20
                --     <--0-> 1 <-2-> 3 <-4-> 5 <-6-->
                [ InputEl a
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 0))    0
                          , Fact_Point   [] 0                             1
                          , Fact_SpanExc [] (spanExc (Just 0) (Just 10))  2
                          , Fact_Point   [] 10                            3
                          , Fact_SpanExc [] (spanExc (Just 10) (Just 20)) 4
                          , Fact_Point   [] 20                            5
                          , Fact_SpanExc [] (spanExc (Just 20) Nothing)   6
                          ]
                    )
                -- time:        5        10        25
                --     <--10-> 11 <-12-> 13 <-14-> 15 <-16-->
                ,  InputEl b
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 5))    10
                          , Fact_Point   [] 5                             11
                          , Fact_SpanExc [] (spanExc (Just 5) (Just 10))  12
                          , Fact_Point   [] 10                            13
                          , Fact_SpanExc [] (spanExc (Just 10) (Just 25)) 14
                          , Fact_Point   [] 25                            15
                          , Fact_SpanExc [] (spanExc (Just 25) Nothing)   16
                          ]
                    )
                -- time:        7        10        25
                --     <--20-> 21 <-22-> 23 <-24-> 25 <-26-->
                ,  InputEl c
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 7))    20
                          , Fact_Point   [] 7                             21
                          , Fact_SpanExc [] (spanExc (Just 7) (Just 10))  22
                          , Fact_Point   [] 10                            23
                          , Fact_SpanExc [] (spanExc (Just 10) (Just 25)) 24
                          , Fact_Point   [] 25                            25
                          , Fact_SpanExc [] (spanExc (Just 25) Nothing)   26
                          ]
                    )
                -- time: --0--2-----6-----10-20-25---30--
                -- (1) -------2-----3------1--_--2----1--
                ,  InputEl switch
                    (Left [ Fact_SpanExc [] (spanExc Nothing (Just 0))    Nothing
                          , Fact_Point   [] 0                             Nothing
                          , Fact_SpanExc [] (spanExc (Just 0) (Just 2))   Nothing
                          , Fact_Point   [] 2                             (Just 2)
                          , Fact_SpanExc [] (spanExc (Just 2) (Just 6))   Nothing
                          , Fact_Point   [] 6                             (Just 3)
                          , Fact_SpanExc [] (spanExc (Just 6) (Just 10))  Nothing
                          , Fact_Point   [] 10                            (Just 1)
                          , Fact_SpanExc [] (spanExc (Just 10) (Just 20)) Nothing
                          -- Unknown at t=20
                          , Fact_SpanExc [] (spanExc (Just 20) (Just 25)) Nothing
                          , Fact_Point   [] 25                            (Just 2)
                          , Fact_SpanExc [] (spanExc (Just 25) (Just 30)) Nothing
                          , Fact_Point   [] 30                            (Just 1)
                          , Fact_SpanExc [] (spanExc (Just 30) Nothing)   Nothing
                          ]
                    )
                -- time:   0       2         5         6         7        10       20      25        30
                -- prevE 1 switch:
                --   <-1-> 1 <-1-> 1 <- 2->  2 <- 2->  2 <- 3->  3 <- 3->  3 <-1->  _ <-_-> _ <- 2->  2 <-1-->
                -- out:
                --   <-0-> 1 <-2-> 2 <-10-> 11 <-12-> 12 <-20-> 21 <-22-> 23 <-4->  5 <-_-> _ <-16-> 16 <-6-->
                , InputEl out
                    (Right $ do
                        switchVal <- prevE 1 switch
                        getV $ case switchVal of
                                1 -> a
                                2 -> b
                                3 -> c
                                x -> error $ "Unexpected switch value of: " ++ show x
                    )
                ]

        lookupVKB (-1) out kb @?= Known 0
        lookupVKB 0  out kb @?= Known 1
        lookupVKB 1  out kb @?= Known 2
        lookupVKB 2  out kb @?= Known 2
        lookupVKB 3  out kb @?= Known 10
        lookupVKB 5  out kb @?= Known 11
        lookupVKB 6  out kb @?= Known 12
        lookupVKB 7  out kb @?= Known 21
        lookupVKB 8  out kb @?= Known 22
        lookupVKB 10 out kb @?= Known 23
        lookupVKB 15 out kb @?= Known 4
        lookupVKB 20 out kb @?= Known 5
        lookupVKB 23 out kb @?= Unknown
        lookupVKB 25 out kb @?= Unknown
        lookupVKB 27 out kb @?= Known 16
        lookupVKB 30 out kb @?= Known 16
        lookupVKB 35 out kb @?= Known 6
    ]
  ]

showDerivationStack :: Time -> VIx a -> KnowledgeBase -> String
showDerivationStack t eix kn = case lookupVKBTrace t eix kn of
    Unknown -> "Unknown"
    Known dtrace -> "\n" ++ (unlines $ reverse $ dtrace)

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
--         occ <- getV sourceEvent1
--         return $ ("hello " ++) <$> occ

--     -- Map a mapped event
--     , mappedEvent1x = event $ do
--         occ <- getV mappedEvent1
--         return $ ("x" ++) <$> occ

--     -- Combine multiple events.
--     , simultaneousEvent = event $ do
--         occA <- getV sourceEvent1
--         occB <- getV sourceEvent2
--         return $ (++) <$> occA <*> occB

--       -- TODO How do we implement step correctly? We should support both:
--       --   * refer to previous value of this behavior (getB steppedSE1). I think
--       --     this is currently broken
--       --     * maybe `foldB` should always be given the previous value
--       --       (implemented with getB)? And cases that don't want the previous
--       --       value should use `step` or `behavior`
--       --   * Allow this rule to return MaybeChange.
--     , steppedSE1 = foldB "init" $ do
--         occ <- getV sourceEvent1
--         oldVal <- getB steppedSE1
--         return (fromMaybe oldVal occ)

--     -- , steppedSE1' = step "init" $ do
--     --     occ <- getV sourceEvent1
--     --     return occ

--     , steppedSimultaneousEvent = foldB "init" $ do
--         occ <- getV simultaneousEvent
--         oldVal <- getB steppedSimultaneousEvent
--         return (fromMaybe oldVal occ)

--     -- , steppedSimultaneousEvent' = step "init" $ do
--     --     occ <- getV simultaneousEvent
--     --     return occ
--     }

