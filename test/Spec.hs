
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
    -- , testGroup "Intersect (AllOr RightSpace) (AllOr LeftSpace)"
    --   [ testProperty "intersect" (\ a (Positive b))
    --   ]
    ]
  , testGroup "Gate"
    [ testProperty "Eq reflective" (\ (x :: Behavior Int) -> x == x)
    , testProperty "Eq step ()" (\ (x :: Event ()) -> step () x == pure ())
    , testProperty "listToE == eventToList" (\ (x :: Event Int) -> eventToList (listToE (eventToList x)) == eventToList x)
    , testCase "updatesToEvent lazyness" $ do
      let x = take 3 $ eventToList $ updatesToEvent
                [ listToEPart
                  [ ( spanIncExc (Just 2) (Just $ delay 10),
                      [ (2,"b")
                      , (10,"c")
                      ]
                    )
                  ]
                , listToEPart
                  [ ( spanIncExc (Just 1) (Just 2),
                      [ (1,"a")
                      ]
                    )
                  ]
                , listToEPart
                  [ ( spanIncExc Nothing (Just 1),
                      []
                    )
                  ]
                , lazinessErr -- Simulate blocking IO that me must not evaluate.
                ]
      x @?= [(1,"a"), (2,"b"), (10,"c")]

    -- , testCase "listToB" $ do
    --   let b = listToB "0" [(0,"a"), (10, "b"), (20, "c")]
    --   sampleB b (-1) @=? "0"
    --   sampleB b 0 @=? "0"
    --   sampleB b 1 @=? "a"
    --   sampleB b 10 @=? "a"
    --   sampleB b 15 @=? "b"
    --   sampleB b 20 @=? "b"
    --   sampleB b 21 @=? "c"
    ]
      -- , testGroup "Source Event"
      --     [ testCase "fire" $ do
      --   (fire, e) <- sourceEvent
      --   fire 2  3 "b" 4
      --   fire 4  5 "c" 6
      --   fire 0  1 "c" 2
      --   fire 100  101 "c" 102
      --   fire 20  21 "c" 22
      --     , testCase "full event history" $ do
      --   (fire, e) <- sourceEvent
      --   fire X_NegInf 1 "a" 2
      --   fire 2  3 "b" 4
      --   fire 4  5 "c" 5
      --   fire 5  6 "d" X_Inf
      --   eventToList e @?= [ (1, "a")
      --         , (3, "b")
      --         , (5, "c")
      --         , (6, "d")
      --         ]
      --     ]
    ]

lazinessErr = error "A value was evaluated unexpectedly"

data Nodes1 = Nodes1_A