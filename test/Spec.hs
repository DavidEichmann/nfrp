
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Control.Monad (when)
import Data.Maybe (isJust, isNothing)
-- import Data.Serialize (Serialize)
-- import Data.Dynamic
-- import qualified Data.Map as M
-- import GHC.Generics (Generic)
-- import qualified Data.Time as Time
import qualified System.Timeout as Sys

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
    , testProperty "DI_JustAfter t == delay (DI_JustAfter t)"
      (\ t -> DI_JustAfter t == delay (DI_JustAfter t))
    ]
  , testGroup "Span"
    [ testProperty "spanIncExc"
        (\ loMay hiMay ->  let s = spanIncExc loMay hiMay in case (loMay, hiMay) of
              (Just lo, Just hi) -> lo < hi ==> s == s
              _ -> property (s == s)
        )
    , testProperty "LeftSpace intersect with allT LeftSpace is self"
        (\ (l :: LeftSpace) -> (All :: AllOr LeftSpace) `intersect` l == l)
    , testProperty "RightSpace intersect with allT RightSpace is self"
        (\ (l :: RightSpace) -> (All :: AllOr RightSpace) `intersect` l == l)
    , testProperty "span intersect self is self"
        (\ (s :: Span) -> s `intersect` s == Just s)
    , testProperty "span diff span -> all endsOn eachother"
        (\ (s1 :: Span) (s2 :: Span) -> case s1 `difference` s2 of
            (Just l, Just r) -> property (isJust (l `endsOn` s2) && isJust (s2 `endsOn` r))
            _ -> property Discard
        )
    ]
  , testGroup "Gate"
    [ testProperty "Eq reflective" (\ (x :: Behavior Int) -> x == x)
    , testProperty "Eq step ()" (\ (x :: Event ()) -> step () x == pure ())
    , testProperty "listToE == eventToList" (\ (x :: Event Int) -> eventToList (listToE (eventToList x)) == eventToList x)
    , testCase "updatesToEvent lazyness" $ do
      let x = take 3 $ eventToList $ updatesToEvent
                [ listToEPart
                  [ ( spanFromIncToInc 2 10,
                      [ (2,"b")
                      , (10,"c")
                      ]
                    )
                  ]
                , listToEPart
                  [ ( spanFromIncToExc 1 2,
                      [ (1,"a")
                      ]
                    )
                  ]
                , listToEPart
                  [ ( spanToExc 1,
                      []
                    )
                  ]
                , lazinessErr -- Simulate blocking IO that me must not evaluate.
                ]
      x @?= [(1,"a"), (2,"b"), (10,"c")]

    , testCase "listToB" $ do
        let b = listToB "0" [(0,"a"), (10, "b"), (20, "c")]
        lookupB (-1) b @=? "0"
        lookupB 0 b @=? "0"
        lookupB 1 b @=? "a"
        lookupB 10 b @=? "a"
        lookupB 15 b @=? "b"
        lookupB 20 b @=? "b"
        lookupB 21 b @=? "c"
    ]
    , testGroup "Source Event"
        [ testCase "Full history case" $ timeout $ do
            (fire, e) <- sourceEvent
            fire (listToEPart [(spanToExc            4 , [(0,"a"), (3,"b")])])
            fire (listToEPart [(spanFromIncToExc 4   6 , [])])
            fire (listToEPart [(spanFromIncToInc 6   10, [(6,"c"), (7,"d")])])
            fire (listToEPart [(spanFromExcToExc 10  22, [(11,"e")])])
            fire (listToEPart [(spanFromIncToExc 22  90, [(25,"f")])])
            fire (listToEPart [(spanFromInc      90    , [(1000,"g")])])
            eventToList e @?=
                  [ (0, "a")
                  , (3, "b")
                  , (6, "c")
                  , (7, "d")
                  , (11, "e")
                  , (25, "f")
                  , (1000, "g")
                  ]
        -- This isn't terminating :-(
        -- , testProperty "Full history ordered but random." $ \ (OrderedFullUpdates (ups :: [(Span, [(Time, Int)])])) -> ioProperty . timeout $ do
        --     (fire, e) <- sourceEvent
        --     mapM_ fire [listToEPart [up] | up <- ups]
        --     eventToList e @?= concatMap snd ups
        ]
    ]

lazinessErr :: a
lazinessErr = error "A value was evaluated unexpectedly"

-- Evaluate with a standard small timeout
timeout :: Assertion -> Assertion
timeout go = do
  evalMay <- Sys.timeout (100000) go
  when (isNothing evalMay) (assertFailure "Timeout!")
  return ()

-- sToNs :: Int -> Int
-- sToNs s = s * (1000000)
