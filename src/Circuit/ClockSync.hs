{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Module for clock synchronization
module Circuit.ClockSync
  ( TimeEstimator(..)
  , SimpleTimeEstimator
  , simpleTimeEstimator
  ) where

import qualified Data.Time as Time

class TimeEstimator te where
  setLatestSample :: te -> (Time.UTCTime, Time.UTCTime) -> te
  estimateTime :: te -> Time.UTCTime -> (Time.UTCTime, te)

-- TODO a more sufisticated clock estimator! Perhaps estimate clock drift.
-- | Time Estimator assumes that:
--      localClock = serverClock + offset
-- where offset is constant
data SimpleTimeEstimator =
  SimpleTimeEstimator (Time.UTCTime, Time.UTCTime) -- ^ latest sample used to adjust current estimate.
                      [(Time.UTCTime, Time.UTCTime)] -- ^ Committed (local, estimated server time) samples, latest at head. All estimates before and equal the head local time are fixed.

simpleTimeEstimator :: (Time.UTCTime, Time.UTCTime) -> SimpleTimeEstimator
simpleTimeEstimator initialSample = SimpleTimeEstimator initialSample []

instance TimeEstimator SimpleTimeEstimator where
  setLatestSample (SimpleTimeEstimator _ commited) sample =
    SimpleTimeEstimator sample commited
  -- | Estimate server time from client time and fix to that time
  estimateTime te@(SimpleTimeEstimator latestSample commited) local =
    case commited of
      [] ->
        let estimate = estimateTimeSimple latestSample local
        in (estimate, SimpleTimeEstimator latestSample [(local, estimate)])
      (commit0@(local0, estimate0):commitedRest) ->
        if | local == local0 -> (estimate0, te)
           | local < local0 ->
             let estimate =
                   estimateTimeFromCommited
                     local
                     (local0, estimate0)
                     commitedRest
             in ( estimate
                , SimpleTimeEstimator
                    latestSample
                    ((local, estimate) : commited))
           | otherwise ->
             let sampleEstimateTime = estimateTimeSimple latestSample local
                 commitEstimateTime = estimateTimeSimple commit0 local
                 estimateFromCommitAWithRate rate =
                   ((local `Time.diffUTCTime` local0) * rate) `Time.addUTCTime`
                   estimate0
                 estimate =
                   if commitEstimateTime < sampleEstimateTime
            -- If behind, then move at maxSyncRate till synched
                     then min
                            sampleEstimateTime
                            (estimateFromCommitAWithRate maxSyncRate)
            -- Else move at minSyncRate till synched
                     else max
                            sampleEstimateTime
                            (estimateFromCommitAWithRate minSyncRate)
          -- Get rate
          -- correctionTargetLocalTime = syncCorrectionTime `Time.addUTCTime` localSample
          -- correctionTargetEstimateTime = estimateTimeSimple latestSample correctionTargetLocalTime
          -- unclampedCorrectionRate = (correctionTargetEstimateTime `Time.diffUTCTime` estimate0) / syncCorrectionTime
          -- correctionRate = max minSyncRate (min unclampedCorrectionRate maxSyncRate)
          -- -- find time at which synch is achieved. a rate of 1 is used after this point.
          -- syncAchievedLocalTime =
             in ( estimate
                , SimpleTimeEstimator
                    latestSample
                    ((local, estimate) : commited))
      -- | Minimum rate of clock (server clock rate / client clock rate) during syncCorrectionTime
    where
      minSyncRate :: Time.NominalDiffTime
      minSyncRate = 0.5
      -- | Maximum rate of clock (server clock rate / client clock rate) during syncCorrectionTime
      maxSyncRate :: Time.NominalDiffTime
      maxSyncRate = 2
      estimateTimeFromCommited ::
           Time.UTCTime
        -> (Time.UTCTime, Time.UTCTime)
        -> [(Time.UTCTime, Time.UTCTime)]
        -> Time.UTCTime
      estimateTimeFromCommited local' commitA [] =
        estimateTimeSimple commitA local'
      estimateTimeFromCommited local' (localB, estimateB) (commitA@(localA, estimateA):commits)
        | localA == local' = estimateA
        | localA > local' = estimateTimeFromCommited local' commitA commits
        | localB < local' =
          error
            "estimateTimeFromCommited expects local to be within or before the committed estimates"
        | otherwise =
          let dEstimatePerDLocal =
                (estimateB `Time.diffUTCTime` estimateA) /
                (localB `Time.diffUTCTime` localA)
              localTimePastA = local' `Time.diffUTCTime` localA
          in (dEstimatePerDLocal * localTimePastA) `Time.addUTCTime` estimateA
      estimateTimeSimple ::
           (Time.UTCTime, Time.UTCTime) -> Time.UTCTime -> Time.UTCTime
      estimateTimeSimple (local0, server0) local' =
        let offset = local0 `Time.diffUTCTime` server0
        in negate offset `Time.addUTCTime` local'
