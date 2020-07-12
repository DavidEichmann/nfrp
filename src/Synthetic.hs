{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Synthetic where

import qualified GHC.Generics as GHC
import Control.Monad (when)
import Data.Kind (Type)
import Data.Maybe (catMaybes, isJust, isNothing, fromMaybe)

-- import NFRP
-- import FRP
import Time (Time)
import TimeSpan
import Theory (VIx(..))
import Theory as T
import TheoryFast as TF
-- import KnowledgeBase
-- import KnowledgeBase.Timeline
import System.Environment

-- | Synthetic inputs and VIx/times that should be sampled
syntheticN :: Int -> ([VIx Int], [Time], Inputs)
syntheticN n =
    ( vixs
    , sampleTimes
    , [ InputEl vix $ if i < n
            -- Source Value
            then Left
                [ case ts of
                    Left t      -> Fact_Point [] t (negate $ (i * timesN) + x)
                    Right tspan -> Fact_SpanExc [] tspan ((i * timesN) + x)
                | (ts, x) <- zip times [0..]
                ]
            -- Derived Value
            else Right $ do
                -- Depend on lower ix values.
                x <- sum <$> mapM (getV . VIx) [0..(i-1)]

                -- Depend on (prevV) higher ix odd values.
                y <- sum . catMaybes <$> mapM (\j -> prevVWhere (VIx j) (\v -> if odd v then Just v else Nothing)) [(i+1)..m]

                return (x+y)

        | vix@(VIx i) <- vixs
        ]
    )
    where
    vixs = VIx <$> [0..m]

    m = (2 * n) - 1

    timesN :: Num a => a
    timesN = 100

    timeStep :: Num a => a
    timeStep = 10

    sampleTimes
        = -1
        : 0
        : timesN * timeStep + 1
        : concat
            [ [ tLo
              , tMid
              ]
            | i <- [0..(timesN-1)]
            , let tLo = i * timeStep
            , let tMid = tLo + 1
            ]

    times :: [Either Time SpanExc]
    times
        = Right (spanExc Nothing (Just 0))
        : Left (timesN * timeStep)
        : Right (spanExc (Just (timesN * timeStep)) Nothing)
        : concat
            [ [ Left tLo
              , Right (spanExc (Just tLo) (Just tHi))
              ]
            | i <- [0..(timesN-1)]
            , let tLo = i * timeStep
            , let tHi = (i + 1) * timeStep
            ]