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
import Theory (ValueM(Pure), MaybeOcc(..), pattern NoOcc, Inputs, InputEl(..), EIx(..), VFact(..), prevV, getE)

-- | Synthetic inputs and EIx/times that should be sampled
syntheticN
  :: Int -- ^ Number of EIx
  -> Int -- ^ Number of source event occurrence times
  -> ([EIx Int], [Time], Inputs)
syntheticN nE nT =
  ( vixs
  , sampleTimes
  , [ InputEl vix
      (if isLowIx
        -- Source Value
        then
          [ case ts of
            Left t      -> VFact_Occ [] t (negate $ (i * timesN) + x)
            Right tspan -> VFact_NoOcc [] (DS_SpanExc tspan)
          | (ts, x) <- zip times [0..]
          ]
        -- Derived Value
        else []
      )
      (if isLowIx
      -- Source Value
      then Nothing
      -- Derived Value
      else Just $ do
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
      )

    | vix@(EIx i) <- vixs
    , let isLowIx = i < nE
    ]
  )
  where
  vixs = EIx <$> [0..m]

  m = (2 * nE) - 1

  timesN :: Num a => a
  timesN = fromIntegral nT

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