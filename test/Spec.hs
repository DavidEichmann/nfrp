
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Data.Maybe (isJust)
-- import Data.Serialize (Serialize)
-- import Data.Dynamic
-- import qualified Data.Map as M
-- import GHC.Generics (Generic)
-- import qualified Data.Time as Time

import NFRP
import Time

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "lcTransaction"
    [ testGroup "TimeD"
        [ testProperty "DI_Exactly t < DI_JustAfter t"
                (\ t -> DI_Exactly t < DI_JustAfter t)
        , testProperty "DI_Exactly t < DI_Inf"
                (\ t -> DI_Exactly t < DI_Inf)
        , testProperty "DI_JustAfter t < DI_Inf"
                (\ t -> DI_JustAfter t < DI_Inf)
        , testProperty "DI_JustAfter t == delayTime (DI_JustAfter t)"
                (\ t -> DI_JustAfter t == delayTime (DI_JustAfter t))
        ]
    , testGroup "Gate"
        [ testProperty "Eq reflective" (\ (x :: Behavior Int) -> x == x)
        , testProperty "Eq step ()" (\ (x :: Event ()) -> step () x == pure ())
        , testProperty "listToE == eventToList" (\ (x :: Event Int) -> eventToList (listToE (eventToList x)) == eventToList x)
        , testCase "updatesToEvent lazyness" $ do
                let x = take 2 $ eventToList $ updatesToEvent [(X_NegInf,2,"a",5),(5,6,"b",7), lazinessErr]
                x @?= [(2,"a"), (6,"b")]

        , testCase "listToB" $ do
                let b = listToB "0" [(0,"a"), (10, "b"), (20, "c")]
                sampleB b (-1) @=? "0"
                sampleB b 0 @=? "0"
                sampleB b 1 @=? "a"
                sampleB b 10 @=? "a"
                sampleB b 15 @=? "b"
                sampleB b 20 @=? "b"
                sampleB b 21 @=? "c"
        ]
    , testGroup "Source Event"
        [ testCase "fire" $ do
            (fire, e) <- sourceEvent
            fire 2  3 "b" 4
            fire 4  5 "c" 6
            fire 0  1 "c" 2
            fire 100  101 "c" 102
            fire 20  21 "c" 22
        , testCase "full event history" $ do
            (fire, e) <- sourceEvent
            fire X_NegInf 1 "a" 2
            fire 2        3 "b" 4
            fire 4        5 "c" 5
            fire 5        6 "d" X_Inf
            eventToList e @?= [ (1, "a")
                              , (3, "b")
                              , (5, "c")
                              , (6, "d")
                              ]
        ]
    ]

lazinessErr = error "A value was evaluated unexpectedly"

data Nodes1 = Nodes1_A