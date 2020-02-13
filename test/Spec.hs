
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
    , testGroup "Behavior"
        [ testProperty "Eq reflective" (\ (x :: Behavior Int) -> x == x)
        , testProperty "Eq step ()" (\ (x :: Event ()) -> step () x == pure ())
        --     testProperty "instantaneousBMap maxT"
        --     (\ t (x :: Int) -> let bmap = instantaneousBMap (toTime t) x
        --         in gateMaxT bmap == Just (DI_Exactly t)
        --     )
        -- , testProperty "instantaneousBMap maxT"
        --     (\ t (x :: Int) -> let bmap = instantaneousBMap (toTime t) x
        --         in gateMaxT bmap == Just (DI_Exactly t)
        --     )
        -- , testProperty "lookupBMap"
        --     (\ (minT :: Time) (x :: Int) -> do
        --         duration <- choose (10, 100)
        --         let minT' = DI_Exactly minT
        --             maxT' = DI_Exactly (minT + duration)
        --             bmap = spanBMap minT' x maxT'
        --         return (lookupBMap (DI_Exactly $ minT+(duration `div` 2)) bmap == Just x)
        --     )
        -- , testProperty "lookupBMap maxT is Just"
        --     (\ (bmap :: BMap Int) -> case gateMaxT bmap of
        --             Nothing -> property Discard
        --             Just t -> property $ isJust (lookupBMap t bmap)
        --     )
        -- , testCase "Some BMap unions" $ do
        --     let
        --         a = spanBMap (DI_Exactly 0) "a" (DI_Exactly 10)
        --         b = spanBMap (DI_Exactly 10) "b" (DI_Exactly 20)
        --         c = spanBMap (DI_JustAfter 20) "c" (DI_Exactly 30)
        --         abc = a `gateUnion` b `gateUnion` c
        --     lookupBMap (DI_Exactly (-1)) abc @?= Nothing
        --     lookupBMap (DI_Exactly 0) abc @?= Just "a"
        --     lookupBMap (DI_Exactly 5) abc @?= Just "a"
        --     lookupBMap (DI_Exactly 10) abc @?= Just "b"
        --     lookupBMap (DI_Exactly 15) abc @?= Just "b"
        --     lookupBMap (DI_Exactly 20) abc @?= Nothing
        --     lookupBMap (DI_Exactly 25) abc @?= Just "c"
        --     lookupBMap (DI_Exactly 30) abc @?= Nothing
        --     lookupBMap (DI_Exactly 31) abc @?= Nothing
        ]

    -- -- TODO I need to work toward having pure tests for live circuits. This is a good start, but it's super inconvenient
    -- -- to define a new test.
    -- ^^^^^ TODO

    -- , testGroup "Live Circuit"
    --     [ testGroup "lcTransaction"
    --         [ testCase "A" $ do
    --             let (circuit, _listeners, SourceEvent Nodes1_A eIx) = buildCircuit $ do
    --                     (se, e) <- newSourceEvent Nodes1_A
    --                     b <- beh (step "a" e)
    --                     return (se, b)
    --                 (lc0, ups0) = mkLiveCircuit Nodes1_A circuit
    --                 (lc1, ups1) = lcTransaction
    --                     lc
    --                     [UpdateListE eIx (spanEMap (Just 0) [(1, "b"), (3, "d"), (4, "e")] (Just 10))]
    --             ups1 @?= []
    --             return ()
    --         ]
    --     ]
    ]

data Nodes1 = Nodes1_A