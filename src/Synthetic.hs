{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Synthetic where

import Data.Maybe (catMaybes)

import Time (Time)
import TimeSpan
import Theory (ValueM(Pure), MaybeOcc(..), pattern NoOcc, Inputs, InputEl(..), EIx(..), Fact(..), prevV, getE)

-- | Synthetic inputs and EIx/times that should be sampled
syntheticN :: Int -> ([EIx Int], [Time], Inputs)
syntheticN n =
  ( vixs
  , sampleTimes
  , [ InputEl vix $ if i < n
      -- Source Value
      then Left
        [ case ts of
          Left t      -> Fact_Occ [] t (negate $ (i * timesN) + x)
          Right tspan -> Fact_NoOcc [] (DS_SpanExc tspan)
        | (ts, x) <- zip times [0..]
        ]
      -- Derived Value
      else Right $ do
        -- Depend on lower ix values.
        xs <- catMaybes . fmap maybeOccToMaybe <$> mapM (getE . EIx) [0..(i-1)]
        if null xs
          then Pure NoOcc
          else do
            let x = sum xs

            -- Depend on (prevV) higher ix odd values.
            y <- sum . catMaybes <$> mapM
                                      (\j -> prevV (EIx j))
                                      [(i+1)..m]

            return (x+y)

    | vix@(EIx i) <- vixs
    ]
  )
  where
  vixs = EIx <$> [0..m]

  m = (2 * n) - 1

  timesN :: Num a => a
  timesN = 100

  timeStep :: Num a => a
  timeStep = 10

  sampleTimes
    = concat
      [ [ tLo
        , tMid
        ]
      | i <- [(-1)..timesN]
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
      , let tHi = tLo + timeStep
      ]