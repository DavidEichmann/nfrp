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
import qualified System.Timeout as Sys

import NFRP
import FRP
import Time
import TimeSpan

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
  , testGroup "Gate"
    [ testProperty "Eq reflective" (\ (x :: Behavior Int) -> x == x)
    , testProperty "Eq step ()" (\ (x :: Event ()) -> step () x == pure ())
    , testProperty "listToE == eventToList" (\ (x :: Event Int) -> eventToList (listToE (eventToList x)) == eventToList x)
    , testCase "updatesToEvent lazyness" $ do
      let x = take 3 $ eventToList $ updatesToEvent $ concat
                [ listToPartialE (Just 1) (Just 10)
                    [ (2,"b")
                    , (10,"c")
                    ]
                , listToPartialE (Just 0) (Just 1)
                    [ (1,"a") ]
                , listToPartialE Nothing (Just 0) []
                , lazinessErr -- Simulate blocking IO that me must not evaluate.
                ]
      x @?= [(1,"a"), (2,"b"), (10,"c")]

    , testCase "listToB" $ do
        let b = listToB "0" [(0,"a"), (10, "b"), (20, "c")]
        lookupB (-1) b @=? "0"
        lookupB (X_JustBefore 0) b @=? "0"
        lookupB 0 b @=? "a"
        lookupB 1 b @=? "a"
        lookupB (X_JustBefore 10) b @=? "a"
        lookupB 10 b @=? "b"
        lookupB 15 b @=? "b"
        lookupB (X_JustBefore 20) b @=? "b"
        lookupB 20 b @=? "c"
        lookupB 21 b @=? "c"
    ]

    , testCase "instance Applicative Behavior" $ do
        let a = listToB ("0"++) [(1,("1"++)),        (3,("3"++))        ]
            b = listToB "a"     [            (2,"b"),            (4,"c")]
            c = a <*> b
        lookupB (-1)      c @?= "0a"
        lookupB (X_JustBefore 1) c @?= "0a"
        lookupB 1         c @?= "1a"
        lookupB (delay 1) c @?= "1a"
        lookupB (X_JustBefore 2) c @?= "1a"
        lookupB 2         c @?= "1b"
        lookupB (delay 2) c @?= "1b"
        lookupB (X_JustBefore 3) c @?= "1b"
        lookupB 3         c @?= "3b"
        lookupB (delay 3) c @?= "3b"
        lookupB (X_JustBefore 4) c @?= "3b"
        lookupB 4         c @?= "3c"
        lookupB (delay 4) c @?= "3c"
        lookupB 5         c @?= "3c"

    , testProperty "instance Applicative Behavior fully evaluate" $ \ (a :: Behavior Int) b ->
        alwaysB (\x -> x == 0 || x /= 0) ((+) <$> a <*> b)

    , testGroup "Source Event"
        [ testCase "Full history case" $ timeout $ do
            (fire, e) <- sourceEvent
            fire (listToPartialE  Nothing    (Just 4)  [(0,"a"), (4,"b")])
            fire (listToPartialE  (Just 4)   (Just 6)  [])
            fire (listToPartialE  (Just 6)   (Just 10) [(7,"c"), (10,"d")])
            fire (listToPartialE  (Just 10)  (Just 22) [(11,"e")])
            fire (listToPartialE  (Just 22)  (Just 90) [(25,"f")])
            fire (listToPartialE  (Just 90)  Nothing   [(1000,"g")])
            eventToList e @?=
                  [ (0, "a")
                  , (4, "b")
                  , (7, "c")
                  , (10, "d")
                  , (11, "e")
                  , (25, "f")
                  , (1000, "g")
                  ]

        , testCase "instance Applicative Behavior lazy" $ timeout $ do
            (fire1, e1) <- sourceEvent
            (fire2, e2) <- sourceEvent
            let b = (++) <$> step "a" e1 <*> step "1" e2

            fire1 (listToPartialE  Nothing   (Just 0)  [])
            fire2 (listToPartialE  Nothing   (Just 0)  [])
            lookupB (X_JustBefore 0)  b @?= "a1"
            lookupB        0  b @?= "a1"

            fire1 (listToPartialE  (Just 0)  (Just 5)  [(1,"b")])
            fire2 (listToPartialE  (Just 0)  (Just 5)  [(1,"2")])
            lookupB (X_JustBefore 1)  b @?= "a1"
            lookupB        1  b @?= "b2"
            lookupB (delay 1) b @?= "b2"

            fire1 (listToPartialE  (Just 12) (Just 15) [(13,"d")])
            fire2 (listToPartialE  (Just 12) (Just 15) [(13,"4")])
            lookupB (delay 13) b @?= "d4"

            fire1 (listToPartialE  (Just 5)  (Just 7)  [])
            fire2 (listToPartialE  (Just 5)  (Just 9)  [(8,"3")])
            fire1 (listToPartialE  (Just 7)  (Just 12) [(11,"c")])
            fire2 (listToPartialE  (Just 9)  (Just 12) [])
            lookupB (X_JustBefore 8)  b @?= "b2"
            lookupB        8   b @?= "b3"
            lookupB (delay 8)  b @?= "b3"
            lookupB (X_JustBefore 11)  b @?= "b3"
            lookupB        11  b @?= "c3"
            lookupB (delay 11) b @?= "c3"
            lookupB 13 b @?= "d4"

        -- , testCase "step gives delayed knowlage lazy" $ timeout $ do
        --     (fire, e) <- sourceEvent
        --     let b = step "0" e
        --     fire (listToPartialE Nothing (Just 4) [(0,"a"), (3,"b")])
        --     lookupB 0 b @?= "0"
        --     lookupB (X_JustAfter 0) b @?= "a"
        --     lookupB 3 b @?= "a"
        --     lookupB (X_JustAfter 3) b @?= "b"
        --     lookupB 4 b @?= "b"
        --     fire (listToPartialE (Just 4) (Just 5) [(5,"c")])
        --     lookupB (X_JustAfter 4) b @?= "b"
        --     lookupB 5 b @?= "b"
        --     lookupB (X_JustAfter 5) b @?= "c"


        -- This isn't terminating :-(
        , testProperty "Full history random, ordered by time." $ \ (OrderedFullEventParts (ups :: [EventPart Int])) -> ioProperty . timeout $ do
            (fire, e) <- sourceEvent
            mapM_ (\up -> fire [up]) ups
            eventToList e @?= [(t, a) | EventPart_Event t (Just a) <- ups]
        ]
    ]

lazinessErr :: a
lazinessErr = error "A value was evaluated unexpectedly"

-- Evaluate with a standard small timeout
timeout :: Assertion -> Assertion
timeout go = do
  evalMay <- Sys.timeout 100000 go
  when (isNothing evalMay) (assertFailure "Timeout! This could mean a value could not me evaluated. Does it still fail with a larger timeout?")

-- sToNs :: Int -> Int
-- sToNs s = s * (1000000)
