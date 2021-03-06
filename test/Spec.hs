{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import qualified GHC.Generics as GHC
import           Control.Monad (forM_, when)
import           Data.Kind (Type)
import           Data.List (foldl', permutations)
import           Data.Maybe (catMaybes, isJust, isNothing, fromMaybe)
import           Data.Text.Prettyprint.Doc
import qualified System.Timeout as Sys
import           Generics.SOP

-- import NFRP
-- import FRP
import Synthetic
import Time (Time)
import TimeSpan
import Theory
    ( EIx(..)
    , pattern Known
    , pattern Unknown
    , Fact(..)
    , VFact(..)
    , MaybeKnown(..)
    , MaybeOcc(..)
    , Inputs(..)
    , SomeFact(..)
    , DerivationTrace
    , requireE
    , getE
    , currV
    , prevV
    , ValueM(..)
    )
import qualified Theory as T
import TheoryFast (InputEl(..), pattern Occ, pattern NoOcc, maybeOccToMaybe)
import qualified TheoryFast as TF
-- import KnowledgeBase
-- import KnowledgeBase.Timeline

main :: IO ()
main = defaultMain tests

gTest :: forall gKnowledgeBase
    .  Pretty gKnowledgeBase
    => String
    -> (Inputs -> gKnowledgeBase)
    -> (forall a . Time -> EIx a -> gKnowledgeBase -> MaybeKnown (MaybeOcc a))
    -> (forall a . Time -> EIx a -> gKnowledgeBase -> MaybeKnown (DerivationTrace a))
    -> ([SomeFact] -> gKnowledgeBase -> gKnowledgeBase)
    -> TestTree
gTest
    testGroupName
    mkKnowledgeBase
    lookupVKB
    lookupVKBTrace
    insertFacts
    = testGroup testGroupName
      [ testCase "Swap values (transitive prevV self reference, end with NoOcc span)" $ do
        let
            swapE :: EIx ()
            swapE = EIx 1

            a, b :: EIx String
            a = EIx 2
            b = EIx 3

            kb :: gKnowledgeBase
            kb = mkKnowledgeBase
                -- time: --0--------5-----7-----9--------
                --------------------()----()----_________
                [ InputEl swapE
                    [ VFact_NoOcc [] (DS_SpanExc $ spanExc Nothing (Just 5))
                    , VFact_Occ   [] 5 ()
                    , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 5) (Just 7))
                    , VFact_Occ   [] 7 ()
                    , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 7) (Just 9))
                    ]
                    Nothing
                -- time: --0--------5-----7-----9--------
                --------------------y-----x-----_________
                , InputEl a []
                    (Just $ do
                        bVal <- fromMaybe "y" <$> prevV b
                        Occ () <- getE swapE
                        return bVal
                    )
                -- time: --0--------5-----7-----9--------
                --------------------x-----y-----__________
                , InputEl b []
                    (Just $ do
                        bVal <- fromMaybe "x" <$> prevV a
                        Occ () <- getE swapE
                        return bVal
                    )
                ]
            a @?== b = assertEqual (show $ pretty kb) b a

        -- let Known tr = lookupVKBTrace 7 a kb
        -- fail $ unlines $ tr

        lookupVKB 0  a kb @?== Known NoOcc
        lookupVKB 0  b kb @?== Known NoOcc
        lookupVKB 1  a kb @?== Known NoOcc
        lookupVKB 1  b kb @?== Known NoOcc
        lookupVKB 5  a kb @?== Known (Occ "y")
        lookupVKB 5  b kb @?== Known (Occ "x")
        lookupVKB 6  a kb @?== Known NoOcc
        lookupVKB 6  b kb @?== Known NoOcc
        lookupVKB 7  a kb @?== Known (Occ "x")
        lookupVKB 7  b kb @?== Known (Occ "y")
        lookupVKB 8  a kb @?== Known NoOcc
        lookupVKB 8  b kb @?== Known NoOcc
        lookupVKB 9  a kb @?== Unknown
        lookupVKB 9  b kb @?== Unknown
        lookupVKB 10 a kb @?== Unknown
        lookupVKB 10 b kb @?== Unknown


      , testCase "Swap values (transitive prevV self reference)" $ do
        let
          swapE :: EIx ()
          swapE = EIx 1

          a, b :: EIx String
          a = EIx 2
          b = EIx 3

          kb :: gKnowledgeBase
          kb = mkKnowledgeBase
                -- time: --0--------5-----7-----9--------
                --------------------()----()____()_______
                [ InputEl swapE
                    [ VFact_NoOcc [] (DS_SpanExc $ spanExc Nothing (Just 5))
                    , VFact_Occ   [] 5 ()
                    , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 5) (Just 7))
                    , VFact_Occ   [] 7 ()
                    , VFact_Occ   [] 9 ()
                    ]
                    Nothing
                -- time: --0--------5-----7-----9--------
                --------------------y-----x_______________
                , InputEl a []
                    (Just $ do
                        bVal <- fromMaybe "y" <$> prevV b
                        Occ () <- getE swapE
                        return bVal
                    )
                -- time: --0--------5-----7-----9--------
                --------------------x-----y_______________
                , InputEl b []
                    (Just $ do
                        bVal <- fromMaybe "x" <$> prevV a
                        Occ () <- getE swapE
                        return bVal
                    )
                ]

        lookupVKB 0  a kb @?= Known NoOcc
        lookupVKB 0  b kb @?= Known NoOcc
        lookupVKB 1  a kb @?= Known NoOcc
        lookupVKB 1  b kb @?= Known NoOcc
        lookupVKB 5  a kb @?= Known (Occ "y")
        lookupVKB 5  b kb @?= Known (Occ "x")
        lookupVKB 6  a kb @?= Known NoOcc
        lookupVKB 6  b kb @?= Known NoOcc
        lookupVKB 7  a kb @?= Known (Occ "x")
        lookupVKB 7  b kb @?= Known (Occ "y")
        lookupVKB 8  a kb @?= Unknown
        lookupVKB 8  b kb @?= Unknown
        lookupVKB 9  a kb @?= Unknown
        lookupVKB 9  b kb @?= Unknown
        lookupVKB 10 a kb @?= Unknown
        lookupVKB 10 b kb @?= Unknown


      , testCase "Simple 1" $ do
        let eix1, eix2 :: EIx String
            eix1 = EIx 1
            eix2 = EIx 2

            kb :: gKnowledgeBase
            kb = mkKnowledgeBase
                    [ InputEl eix1 [VFact_Occ   [] 1 "Hello"] Nothing
                    , InputEl eix2
                        []
                        (Just $ do
                            xs <- requireE eix1
                            return (xs ++ " World!")
                        )
                    ]

            a @?== b = assertEqual (show $ pretty kb) b a

        lookupVKB 1 eix2 kb @?== Known (Occ "Hello World!")


      , testCase "Simple 2" $ do
        let eix1, eix2, eix3 :: EIx String
            eix1 = EIx 1
            eix2 = EIx 2
            eix3 = EIx 3

            kb :: gKnowledgeBase
            kb = mkKnowledgeBase
                    [ InputEl eix1
                        [ VFact_Occ   [] 1 "Hello"
                        , VFact_Occ   [] 5 "Goodbye"
                        ]
                        Nothing
                    , InputEl eix2
                        []
                        (Just $ do
                            xs <- requireE eix3
                            return (xs ++ "!")
                        )
                    , InputEl eix3
                        []
                        (Just $ do
                            xs <- requireE eix1
                            return (xs ++ " World")
                        )
                    ]
            a @?== b = assertEqual (show $ pretty kb) b a

        -- assertFailure $ show $ pretty kb

        lookupVKB 1 eix2 kb @?== Known (Occ "Hello World!")
        lookupVKB 3 eix2 kb @?== Unknown
        lookupVKB 5 eix2 kb @?== Known (Occ "Goodbye World!")


      , testCase "Simple 3" $ do
        let eix1, eix2, eix3 :: EIx String
            eix1 = EIx 1
            eix2 = EIx 2
            eix3 = EIx 3

            kb :: gKnowledgeBase
            kb = mkKnowledgeBase
                    [ InputEl eix1
                        [ VFact_Occ   [] 1 "Hello"
                        , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 1) (Just 5))
                        , VFact_Occ   [] 5 "Goodbye"
                        ]
                        Nothing
                    , InputEl eix2
                        []
                        (Just $ do
                            xs <- requireE eix3
                            return (xs ++ "!")
                        )
                    , InputEl eix3
                        []
                        (Just $ do
                            xs <- requireE eix1
                            return (xs ++ " World")
                        )
                    ]
            a @?== b = assertEqual (show $ pretty kb) b a

        -- assertFailure $ show $ pretty kb

        lookupVKB 1 eix2 kb @?== Known (Occ "Hello World!")
        lookupVKB 3 eix2 kb @?== Known NoOcc
        lookupVKB 5 eix2 kb @?== Known (Occ "Goodbye World!")


      , testCase "Simple 4" $ do
        let eix1, eix2, eix3 :: EIx String
            eix1 = EIx 1
            eix2 = EIx 2
            eix3 = EIx 3

            kb :: gKnowledgeBase
            kb = mkKnowledgeBase
                    [ InputEl eix1
                        [ VFact_NoOcc [] (DS_SpanExc $ spanExc Nothing (Just 1))
                        , VFact_Occ   [] 1 "Hello"
                        , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 1) (Just 5))
                        , VFact_Occ   [] 5 "Goodbye"
                        ]
                        Nothing
                    , InputEl eix2
                        []
                        (Just $ do
                            xs <- requireE eix3
                            old <- maybe "" (++ " >> ") <$> prevV eix2
                            return (old ++ xs ++ "!")
                        )
                    , InputEl eix3
                        []
                        (Just $ do
                            xs <- requireE eix1
                            return (xs ++ " World")
                        )
                    ]
            a @?== b = assertEqual (show $ pretty kb) b a

        lookupVKB 1 eix3 kb @?== Known (Occ "Hello World")
        lookupVKB 3 eix3 kb @?== Known NoOcc
        lookupVKB 5 eix3 kb @?== Known (Occ "Goodbye World")

        lookupVKB 1 eix2 kb @?== Known (Occ "Hello World!")
        lookupVKB 3 eix2 kb @?== Known NoOcc
        lookupVKB 5 eix2 kb @?== Known (Occ "Hello World! >> Goodbye World!")


      , testCase "Switching" $ do
          let
            a, b, c :: EIx Int
            a      = EIx 1
            b      = EIx 2
            c      = EIx 3

            switch :: EIx Int
            switch = EIx 4

            out :: EIx Int
            out    = EIx 5

            kb :: gKnowledgeBase
            kb = mkKnowledgeBase
                  -- time: --0--2--4--6--8--10-12-14-16---
                  -----------11-12-13-14-15-16-17-18-19---
                  [ InputEl a
                      [ VFact_NoOcc [] (DS_SpanExc $ spanExc Nothing (Just 0))
                            , VFact_Occ [] 0 11
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 0) (Just 2))
                            , VFact_Occ [] 2 12
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 2) (Just 4))
                            , VFact_Occ [] 4 13
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 4) (Just 6))
                            , VFact_Occ [] 6 14
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 6) (Just 8))
                            , VFact_Occ [] 8 15
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 8) (Just 10))
                            , VFact_Occ [] 10 16
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 10) (Just 12))
                            , VFact_Occ [] 12 17
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 12) (Just 14))
                            , VFact_Occ [] 14 18
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 14) (Just 16))
                            , VFact_Occ [] 16 19
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 16) Nothing)
                      ]
                      Nothing
                  -- time: --0--2--4--6--8--10-12-14-16---
                  -----------21-22-23-24-25-26-27-28-29---
                  ,  InputEl b
                      [ VFact_NoOcc [] (DS_SpanExc $ spanExc Nothing (Just 0))
                            , VFact_Occ [] 0 21
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 0) (Just 2))
                            , VFact_Occ [] 2 22
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 2) (Just 4))
                            , VFact_Occ [] 4 23
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 4) (Just 6))
                            , VFact_Occ [] 6 24
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 6) (Just 8))
                            , VFact_Occ [] 8 25
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 8) (Just 10))
                            , VFact_Occ [] 10 26
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 10) (Just 12))
                            , VFact_Occ [] 12 27
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 12) (Just 14))
                            , VFact_Occ [] 14 28
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 14) (Just 16))
                            , VFact_Occ [] 16 29
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 16) Nothing)
                      ]
                      Nothing
                  -- time: --0--2--4--6--8--10-12-14-16---
                  -----------31-32-33-34-35-36-37-38-39---
                  ,  InputEl c
                      [ VFact_NoOcc [] (DS_SpanExc $ spanExc Nothing (Just 0))
                            , VFact_Occ [] 0 31
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 0) (Just 2))
                            , VFact_Occ [] 2 32
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 2) (Just 4))
                            , VFact_Occ [] 4 33
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 4) (Just 6))
                            , VFact_Occ [] 6 34
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 6) (Just 8))
                            , VFact_Occ [] 8 35
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 8) (Just 10))
                            , VFact_Occ [] 10 36
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 10) (Just 12))
                            , VFact_Occ [] 12 37
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 12) (Just 14))
                            , VFact_Occ [] 14 38
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 14) (Just 16))
                            , VFact_Occ [] 16 39
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 16) Nothing)
                      ]
                      Nothing
                  -- time: --0--2--4--6--8--10-12-14-16---
                  -- (1) -------2-----3------1--_--2------
                  ,  InputEl switch
                      [ VFact_NoOcc [] (DS_SpanExc $ spanExc Nothing (Just 0))
                            , VFact_NoOcc [] (DS_Point 0)
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 0) (Just 2))
                            , VFact_Occ [] 2 2
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 2) (Just 6))
                            , VFact_Occ [] 6 3
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 6) (Just 10))
                            , VFact_Occ [] 10 1
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 10) (Just 12))
                            -- Unknown at t=12
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 12) (Just 14))
                            , VFact_Occ [] 14 2
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 14) Nothing)
                      ]
                      Nothing
                  -- time: --0--2--4--6--8--10-12---14-16---
                  -----------11-22-23-34-35-16-_____28-29---
                  , InputEl out
                      []
                      (Just $ do
                          switchVal <- fromMaybe 1 <$> currV switch
                          requireE $ case switchVal of
                                  1 -> a
                                  2 -> b
                                  3 -> c
                                  x -> error $ "Unexpected switch value of: " ++ show x
                      )
                  ]
            a @?== b = assertEqual (show $ pretty kb) b a

          lookupVKB (-1) out kb @?== Known NoOcc
          lookupVKB 0  out kb @?== Known (Occ 11)
          lookupVKB 1  out kb @?== Known NoOcc
          lookupVKB 2  out kb @?== Known (Occ 22)
          lookupVKB 3  out kb @?== Known NoOcc
          lookupVKB 4  out kb @?== Known (Occ 23)
          lookupVKB 5  out kb @?== Known NoOcc
          lookupVKB 6  out kb @?== Known (Occ 34)
          lookupVKB 7  out kb @?== Known NoOcc
          lookupVKB 8  out kb @?== Known (Occ 35)
          lookupVKB 9  out kb @?== Known NoOcc
          lookupVKB 10 out kb @?== Known (Occ 16)
          lookupVKB 11 out kb @?== Known NoOcc
          lookupVKB 12 out kb @?== Unknown
          lookupVKB 13 out kb @?== Unknown
          lookupVKB 14 out kb @?== Known (Occ 28)
          lookupVKB 15 out kb @?== Known NoOcc
          lookupVKB 16 out kb @?== Known (Occ 29)
          lookupVKB 17 out kb @?== Known NoOcc


      , testCase "Synthetic-ish 3" $ do
        let
            eix1, eix2, eix3 :: EIx Int
            eix1 = EIx 1
            eix2 = EIx 2
            eix3 = EIx 3

            kb :: gKnowledgeBase
            kb = mkKnowledgeBase
                    -- time: --0--------5-----7--------------
                    --         2        4     6
                    [ InputEl eix1
                        [ VFact_NoOcc [] (DS_SpanExc $ spanExc Nothing (Just 0))
                            , VFact_Occ   [] 0 2
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 0) (Just 5))
                            , VFact_Occ   [] 5 4
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 5) (Just 7))
                            , VFact_Occ   [] 7 6
                            , VFact_NoOcc [] (DS_SpanExc $ spanExc (Just 7) Nothing)
                        ]
                        Nothing
                    -- time: --0--------5-----7--------------
                    --         2        8    18
                    , InputEl eix2
                        []
                        (Just $ do
                            xs <- catMaybes . fmap maybeOccToMaybe <$> mapM getE [eix1]
                            if null xs
                                then Pure NoOcc
                                else do
                                    y <- sum . catMaybes <$> mapM prevV
                                                                [eix3]
                                    return (sum xs + y)
                        )
                    -- time: --0--------5-----7--------------
                    --         4       12    24
                    , InputEl eix3
                        []
                        (Just $ do
                            xs <- catMaybes . fmap maybeOccToMaybe <$> mapM getE [eix1, eix2]
                            if null xs
                                then Pure NoOcc
                                else do
                                    y <- sum . catMaybes <$> mapM prevV
                                                                []
                                    return (sum xs + y)
                        )
                    ]
            a @?== b = assertEqual (show $ pretty kb) b a

        lookupVKB (-1) eix2 kb @?== Known NoOcc
        lookupVKB 0 eix2 kb @?== Known (Occ 2)
        lookupVKB 2 eix2 kb @?== Known NoOcc
        lookupVKB 5 eix2 kb @?== Known (Occ 8)
        lookupVKB 6 eix2 kb @?== Known NoOcc
        lookupVKB 7 eix2 kb @?== Known (Occ 18)
        lookupVKB 8 eix2 kb @?== Known NoOcc

        lookupVKB (-1) eix3 kb @?== Known NoOcc
        lookupVKB 0 eix3 kb @?== Known (Occ 4)
        lookupVKB 2 eix3 kb @?== Known NoOcc
        lookupVKB 5 eix3 kb @?== Known (Occ 12)
        lookupVKB 6 eix3 kb @?== Known NoOcc
        lookupVKB 7 eix3 kb @?== Known (Occ 24)
        lookupVKB 8 eix3 kb @?== Known NoOcc

      , testCase "Synthetic + Iterative (all permutation are the same)" $ do
        -- Make a empty (of facts) KnowledgeBase and get all source facts.
        let (eixs, testSampleTimes, inputs) = syntheticN 2 2
            factsOrig :: [SomeFact]
            factsOrig = concat
              [ SomeFact eix . Fact_VFact <$> eventFacts
              | InputEl eix eventFacts _ <- inputs
              ]
            emptyInputs = [ InputEl eix [] derMay | InputEl eix _ derMay <- inputs ]
            emptyKb = mkKnowledgeBase emptyInputs

            kbEq :: gKnowledgeBase -> gKnowledgeBase -> Bool
            kbEq a b = and
              [ lookupVKB t eix a == lookupVKB t eix b
              | t <- testSampleTimes
              , eix <- eixs
              ]

            -- use the first permutation of input facts as a reference
            -- Note that the total number of permutations is huge! So we take
            -- only a small subset.
            refInFacts : inFactsPerms
              = factsOrig
              : reverse factsOrig
              : take 10000
                  [p | (p,100) <- zip (permutations factsOrig) (cycle [1..100])]
            apFacts :: [SomeFact] -> gKnowledgeBase
            apFacts fs = foldl' (\kb f -> insertFacts [f] kb) emptyKb fs
            refKb = apFacts refInFacts

        forM_ inFactsPerms $ \fs -> do
          kbEq refKb (apFacts fs) @? "KnowledgeBases Don't match"
      ]


tests :: TestTree
tests = testGroup "NFRP"
  [ gTest "Theory"
         T.mkKnowledgeBase  T.lookupVKB  T.lookupVKBTrace
         T.insertFacts
  , gTest "TheoryFast"
        TF.mkKnowledgeBase TF.lookupVKB TF.lookupVKBTrace
        (TF.insertFacts . TF.listToFacts)
  , testGroup "Model - Event based"

      -- TODO this passes even though the "swap" test cases are failing for just
      -- the TheoryFastVersion. SyntheticN is supposed to be a good
      -- representation of all possibilities. Perhaps we should improve
      -- syntheticN.

      [ let n = 5 in testCase ("TheoryFast vs Theory on Synthetic " ++ show n) $ do
        let (vixs, ts, ins) = syntheticN n 100
            lookupT  = let kb =  T.mkKnowledgeBase ins in \t vix -> T.lookupVKB t vix kb
            lookupTF = let kb = TF.mkKnowledgeBase ins in \t vix ->TF.lookupVKB t vix kb
        sequence_
            [ lookupTF t vix @?= lookupT t vix
            | vix <- vixs
            , t <- ts
            ]
      ]
  ]

--   [ testGroup "Model - Event"
--     [ testCase "GetE Only" $ do
--         let
--           eix1, eix2, eix3 :: EIx (MaybeOcc Int)
--           eix1 = EIx 1
--           eix2 = EIx 2
--           eix3 = EIx 3

--           kb :: T.KnowledgeBase
--           kb = T.mkKnowledgeBase
--                 -- time: --0--------5-----7--------------
--                 --------------------------9______________
--                 [ InputEl eix1
--                     (Left [ VFact_NoOcc [] (spanExc Nothing (Just 7)) NoOcc
--                           , VFact_Occ   [] 7 (Occ 9)
--                           ]
--                     )
--                 -- time: --0--------5-----7--------------
--                 -------------------90____80______________
--                 , InputEl eix2
--                     (Left [ VFact_NoOcc [] (spanExc Nothing (Just 5)) NoOcc
--                           , VFact_Occ   [] 5 (Occ 90)
--                           , VFact_Occ   [] 7 (Occ 80)
--                           ]
--                     )
--                 -- time: --0--------5-----7--------------
--                 ------------------190____189_____________
--                 , InputEl eix3
--                     (Right $ do
--                         e1 <- getE eix1
--                         e2 <- getE eix2
--                         return $ case (e1, e2) of
--                             (NoOcc, NoOcc) -> NoOcc
--                             _ -> Occ $ 100
--                                         + fromMaybe 0 (maybeOccToMaybe e1)
--                                         + fromMaybe 0 (maybeOccToMaybe e2)
--                     )
--                 ]

--         -- T.lookupVKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
--         T.lookupVKB 0 eix3 kb @?= Known NoOcc
--         T.lookupVKB 5 eix3 kb @?= Known (Occ 190)
--         T.lookupVKB 6 eix3 kb @?= Unknown
--         T.lookupVKB 7 eix3 kb @?= Known (Occ 189)
--         T.lookupVKB 8 eix3 kb @?= Unknown

--       , testCase "PrevV Only" $ do
--         let
--           eix1, eix2 :: EIx (MaybeOcc Int)
--           eix1 = EIx 1
--           eix2 = EIx 2

--           kb :: T.KnowledgeBase
--           kb = T.mkKnowledgeBase
--                 -- time: --0--------5-----7--------------
--                 -----------7--------8_____9______________
--                 [ InputEl eix1
--                     (Left [ VFact_NoOcc [] (spanExc Nothing (Just 0)) NoOcc
--                           , VFact_Occ   [] 0 (Occ 7)
--                           , VFact_NoOcc [] (spanExc (Just 0) (Just 5)) NoOcc
--                           , VFact_Occ   [] 5 (Occ 8)
--                           , VFact_Occ   [] 7 (Occ 9)
--                           ]
--                     )
--                 -- time: --0--------5-----7--------------
--                 ---------100------107____________________
--                 , InputEl eix2
--                     (Right $ do
--                         onEvent eix1 $ \_ -> do
--                             e1 <- prevV 0 eix1
--                             return (e1+100)
--                     )
--                 ]

--         -- T.lookupVKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
--         T.lookupVKB (-1) eix2 kb @?= Known NoOcc
--         T.lookupVKB 0 eix2 kb @?= Known (Occ 100)
--         T.lookupVKB 2 eix2 kb @?= Known NoOcc
--         T.lookupVKB 5 eix2 kb @?= Known (Occ 107)
--         T.lookupVKB 6 eix2 kb @?= Unknown
--         T.lookupVKB 7 eix2 kb @?= Unknown
--         T.lookupVKB 8 eix2 kb @?= Unknown


--       , testCase "GetE and PrevV (no self reference)" $ do
--         let
--           eix1, eix2, eix3 :: EIx (MaybeOcc Int)
--           eix1 = EIx 1
--           eix2 = EIx 2
--           eix3 = EIx 3

--           kb :: T.KnowledgeBase
--           kb = T.mkKnowledgeBase
--                 -- time: --0--------5-----7-----9--------
--                 --------------------3-----1----__________
--                 [ InputEl eix1
--                     (Left [ VFact_NoOcc [] (spanExc Nothing (Just 5)) NoOcc
--                           , VFact_Occ   [] 5 (Occ 3)
--                           , VFact_NoOcc [] (spanExc (Just 5) (Just 7)) NoOcc
--                           , VFact_Occ   [] 7 (Occ 1)
--                           , VFact_NoOcc [] (spanExc (Just 7) (Just 9)) NoOcc
--                           ]
--                     )
--                 -- time: --0--------5-----7-----9--------
--                 -------------------90____80____70________
--                 , InputEl eix2
--                     (Left [ VFact_NoOcc [] (spanExc Nothing (Just 5)) NoOcc
--                           , VFact_Occ   [] 5 (Occ 90)
--                           , VFact_Occ   [] 7 (Occ 80)
--                           , VFact_Occ   [] 9 (Occ 70)
--                           ]
--                     )
--                 -- time: --0--------5-----7-----9--------
--                 -------------------190___183___171_______
--                 , InputEl eix3
--                     (Right $ do
--                         e1 <- prevV 0 eix1
--                         e2May <- getE eix2
--                         return $ case e2May of
--                             NoOcc -> NoOcc
--                             Occ e2 -> Occ (e1+e2+100)
--                     )
--                 ]

--         -- T.lookupVKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
--         T.lookupVKB 0 eix3 kb @?= Known NoOcc
--         T.lookupVKB 5 eix3 kb @?= Known (Occ 190)
--         T.lookupVKB 6 eix3 kb @?= Unknown
--         T.lookupVKB 7 eix3 kb @?= Known (Occ 183)
--         T.lookupVKB 8 eix3 kb @?= Unknown
--         T.lookupVKB 9 eix3 kb @?= Known (Occ 171)


--       , testCase "GetE and PrevV (with self reference after onEvent)" $ do
--         let
--           eix1, eix2 :: EIx (MaybeOcc Int)
--           eix1 = EIx 1
--           eix2 = EIx 2

--           kb :: T.KnowledgeBase
--           kb = T.mkKnowledgeBase
--                 -- time: --0--------5-----7-----9--------
--                 --------------------3-----1_____5____
--                 [ InputEl eix1
--                     (Left [ VFact_NoOcc [] (spanExc Nothing (Just 5)) NoOcc
--                           , VFact_Occ   [] 5 (Occ 3)
--                           , VFact_NoOcc [] (spanExc (Just 5) (Just 7)) NoOcc
--                           , VFact_Occ   [] 7 (Occ 1)
--                           , VFact_Occ   [] 9 (Occ 5)
--                           ]
--                     )
--                 -- time: --0--------5-----7-----9--------
--                 --------------------3-----4______________
--                 , InputEl eix2
--                     (Right $ do
--                         onEvent eix1 $ \delta -> do
--                             sumSoFar <- prevV 0 eix2 -- Self reference
--                             return (sumSoFar + delta)
--                     )
--                 ]

--         -- T.lookupVKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
--         T.lookupVKB 0 eix2 kb @?= Known NoOcc
--         T.lookupVKB 5 eix2 kb @?= Known (Occ 3)
--         T.lookupVKB 6 eix2 kb @?= Known NoOcc
--         T.lookupVKB 7 eix2 kb @?= Known (Occ 4)
--         T.lookupVKB 8 eix2 kb @?= Unknown
--         T.lookupVKB 9 eix2 kb @?= Unknown
--         T.lookupVKB 10 eix2 kb @?= Unknown


--       -- | This is the same as the last test, but the order of the GetE and
--       -- PrevV swapped. This is significantly harder for the solver.
--       , testCase "PrevV and GetE (with self reference before onEvent)" $ do
--         let
--           eix1, eix2 :: EIx (MaybeOcc Int)
--           eix1 = EIx 1
--           eix2 = EIx 2

--           kb :: T.KnowledgeBase
--           kb = T.mkKnowledgeBase
--                 -- time: -----------5-----7-----111--------
--                 --------------------3-----1_____5____
--                 [ InputEl eix1
--                     (Left [ VFact_NoOcc [] (spanExc Nothing (Just 5)) NoOcc
--                           , VFact_Occ   [] 5 (Occ 3)
--                           , VFact_NoOcc [] (spanExc (Just 5) (Just 7)) NoOcc
--                           , VFact_Occ   [] 7 (Occ 1)
--                           , VFact_Occ   [] 111 (Occ 5)
--                           ]
--                     )
--                 -- time: -----------5-----7-----111--------
--                 --------------------3-----4______________
--                 , InputEl eix2
--                     (Right $ do
--                         sumSoFar <- prevV 0 eix2 -- Self reference
--                         -- Require happens after self reference which disallows
--                         -- short circuiting when eix1 is not occurring.
--                         onEvent eix1 $ \delta ->
--                             return (sumSoFar + delta)
--                     )
--                 ]

--         -- T.lookupVKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
--         T.lookupVKB 0 eix2 kb @?= Known NoOcc
--         T.lookupVKB 5 eix2 kb @?= Known (Occ 3)
--         T.lookupVKB 6 eix2 kb @?= Known NoOcc
--         T.lookupVKB 7 eix2 kb @?= Known (Occ 4)
--         T.lookupVKB 8 eix2 kb @?= Unknown
--         T.lookupVKB 111 eix2 kb @?= Unknown
--         T.lookupVKB 112 eix2 kb @?= Unknown


--       , testCase "GetE and PrevV (with self reference after onEvent and missing info)" $ do
--         let
--           eix1, eix2 :: EIx (MaybeOcc Int)
--           eix1 = EIx 1
--           eix2 = EIx 2

--           kb :: T.KnowledgeBase
--           kb = T.mkKnowledgeBase
--                 -- time: --0--------5-----7-----9--------
--                 -----------_--------3-----1_____5____
--                 [ InputEl eix1
--                     (Left [ VFact_NoOcc [] (spanExc Nothing (Just 0)) NoOcc
--                           , VFact_NoOcc [] (spanExc (Just 0) (Just 5)) NoOcc
--                           , VFact_Occ   [] 5 (Occ 3)
--                           , VFact_NoOcc [] (spanExc (Just 5) (Just 7)) NoOcc
--                           , VFact_Occ   [] 7 (Occ 1)
--                           , VFact_Occ   [] 9 (Occ 5)
--                           ]
--                     )
--                 -- time: --0--------5-----7-----9--------
--                 -----------_--------_-----_______________
--                 -- Note that because of the use of `onEvent`, exi2 is not a
--                 -- dependency at e.g. t∈{2,6} so we know that the event isn't
--                 -- occurring.
--                 , InputEl eix2
--                     (Right $ do
--                         onEvent eix1 $ \delta -> do
--                             sumSoFar <- prevV 0 eix2 -- Self reference
--                             return (sumSoFar + delta)
--                     )
--                 ]

--         -- T.lookupVKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
--         T.lookupVKB (-1) eix2 kb @?= Known NoOcc
--         T.lookupVKB 0 eix2 kb @?= Unknown
--         T.lookupVKB 1 eix2 kb @?= Known NoOcc
--         T.lookupVKB 5 eix2 kb @?= Unknown
--         T.lookupVKB 6 eix2 kb @?= Known NoOcc
--         T.lookupVKB 7 eix2 kb @?= Unknown
--         T.lookupVKB 8 eix2 kb @?= Unknown
--         T.lookupVKB 9 eix2 kb @?= Unknown
--         T.lookupVKB 10 eix2 kb @?= Unknown

--   , testGroup "Model - Behavior"
--     [ testCase "Switching" $ do
--         let
--           a, b, c :: EIx Int
--           a      = EIx 1
--           b      = EIx 2
--           c      = EIx 3

--           switch :: EIx (MaybeOcc Int)
--           switch = EIx 4

--           out :: EIx Int
--           out    = EIx 5

--           kb :: T.KnowledgeBase
--           kb = T.mkKnowledgeBase
--                 -- time:      0      10      20
--                 --     <--0-> 1 <-2-> 3 <-4-> 5 <-6-->
--                 [ InputEl a
--                     (Left [ VFact_NoOcc [] (spanExc Nothing (Just 0))    0
--                           , VFact_Occ   [] 0                             1
--                           , VFact_NoOcc [] (spanExc (Just 0) (Just 10))  2
--                           , VFact_Occ   [] 10                            3
--                           , VFact_NoOcc [] (spanExc (Just 10) (Just 20)) 4
--                           , VFact_Occ   [] 20                            5
--                           , VFact_NoOcc [] (spanExc (Just 20) Nothing)   6
--                           ]
--                     )
--                 -- time:        5        10        25
--                 --     <--10-> 11 <-12-> 13 <-14-> 15 <-16-->
--                 ,  InputEl b
--                     (Left [ VFact_NoOcc [] (spanExc Nothing (Just 5))    10
--                           , VFact_Occ   [] 5                             11
--                           , VFact_NoOcc [] (spanExc (Just 5) (Just 10))  12
--                           , VFact_Occ   [] 10                            13
--                           , VFact_NoOcc [] (spanExc (Just 10) (Just 25)) 14
--                           , VFact_Occ   [] 25                            15
--                           , VFact_NoOcc [] (spanExc (Just 25) Nothing)   16
--                           ]
--                     )
--                 -- time:        7        10        25
--                 --     <--20-> 21 <-22-> 23 <-24-> 25 <-26-->
--                 ,  InputEl c
--                     (Left [ VFact_NoOcc [] (spanExc Nothing (Just 7))    20
--                           , VFact_Occ   [] 7                             21
--                           , VFact_NoOcc [] (spanExc (Just 7) (Just 10))  22
--                           , VFact_Occ   [] 10                            23
--                           , VFact_NoOcc [] (spanExc (Just 10) (Just 25)) 24
--                           , VFact_Occ   [] 25                            25
--                           , VFact_NoOcc [] (spanExc (Just 25) Nothing)   26
--                           ]
--                     )
--                 -- time: --0--2-----6-----10-20-25---30--
--                 -- (1) -------2-----3------1--_--2----1--
--                 ,  InputEl switch
--                     (Left [ VFact_NoOcc [] (spanExc Nothing (Just 0))    NoOcc
--                           , VFact_Occ   [] 0                             NoOcc
--                           , VFact_NoOcc [] (spanExc (Just 0) (Just 2))   NoOcc
--                           , VFact_Occ   [] 2                             (Occ 2)
--                           , VFact_NoOcc [] (spanExc (Just 2) (Just 6))   NoOcc
--                           , VFact_Occ   [] 6                             (Occ 3)
--                           , VFact_NoOcc [] (spanExc (Just 6) (Just 10))  NoOcc
--                           , VFact_Occ   [] 10                            (Occ 1)
--                           , VFact_NoOcc [] (spanExc (Just 10) (Just 20)) NoOcc
--                           -- Unknown at t=20
--                           , VFact_NoOcc [] (spanExc (Just 20) (Just 25)) NoOcc
--                           , VFact_Occ   [] 25                            (Occ 2)
--                           , VFact_NoOcc [] (spanExc (Just 25) (Just 30)) NoOcc
--                           , VFact_Occ   [] 30                            (Occ 1)
--                           , VFact_NoOcc [] (spanExc (Just 30) Nothing)   NoOcc
--                           ]
--                     )
--                 -- time:   0       2         5         6         7        10       20      25        30
--                 -- prevV 1 switch:
--                 --   <-1-> 1 <-1-> 1 <- 2->  2 <- 2->  2 <- 3->  3 <- 3->  3 <-1->  _ <-_-> _ <- 2->  2 <-1-->
--                 -- out:
--                 --   <-0-> 1 <-2-> 2 <-10-> 11 <-12-> 12 <-20-> 21 <-22-> 23 <-4->  5 <-_-> _ <-16-> 16 <-6-->
--                 , InputEl out
--                     (Right $ do
--                         switchVal <- fromMaybe 1 <$> prevV switch
--                         getE $ case switchVal of
--                                 1 -> a
--                                 2 -> b
--                                 3 -> c
--                                 x -> error $ "Unexpected switch value of: " ++ show x
--                     )
--                 ]

--         T.lookupVKB (-1) out kb @?= Known 0
--         T.lookupVKB 0  out kb @?= Known 1
--         T.lookupVKB 1  out kb @?= Known 2
--         T.lookupVKB 2  out kb @?= Known 2
--         T.lookupVKB 3  out kb @?= Known 10
--         T.lookupVKB 5  out kb @?= Known 11
--         T.lookupVKB 6  out kb @?= Known 12
--         T.lookupVKB 7  out kb @?= Known 21
--         T.lookupVKB 8  out kb @?= Known 22
--         T.lookupVKB 10 out kb @?= Known 23
--         T.lookupVKB 15 out kb @?= Known 4
--         T.lookupVKB 20 out kb @?= Known 5
--         T.lookupVKB 23 out kb @?= Unknown
--         T.lookupVKB 25 out kb @?= Unknown
--         T.lookupVKB 27 out kb @?= Known 16
--         T.lookupVKB 30 out kb @?= Known 16
--         T.lookupVKB 35 out kb @?= Known 6
--     ]
  -- ]

showDerivationStack :: Time -> EIx a -> T.KnowledgeBase -> String
showDerivationStack t eix kn = case T.lookupVKBTrace t eix kn of
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

