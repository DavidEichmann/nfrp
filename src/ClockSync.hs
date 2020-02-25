{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wincomplete-uni-patterns #-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module ClockSync
    ( clockSyncServer
    , clockSyncClient
    , getLocalTime
    ) where

import           Control.Concurrent
import           Control.Concurrent.MVar (MVar, modifyMVar, modifyMVar_, newEmptyMVar, putMVar)
import qualified Control.Concurrent.Chan as C
import           Control.Monad (forever)
import           Data.Ratio
import           Data.Time.Clock.System (SystemTime(..), getSystemTime)

import FRP
import Time

-- | This nodes's local system time.
type LocalTime = Time

-- | The global time we are trying to synchronize with.
type GlobalTime = Time

-- | A Behavior describing how to convert from LocalTime to GlobalTime
type TimeDomainConverter = BehaviorT LocalTime (LocalTime -> GlobalTime)

type Nonce = Int

-- | Used for documentation purposes only.
type EventT    timeDomain a = Event a
type BehaviorT timeDomain a = Behavior a

-- | Approximate time in microseconds that clock sync request should be sent.
clockSyncInterval :: Int
clockSyncInterval = 10000000 -- 10 seconds

clockSyncServer
    :: Chan (LocalTime, GlobalTime)
    -- ^ Chan used to send responses. Contains the client's local times (when
    -- the request was sent), and this server's (global) time (when it received
    -- the request).
    -> Chan LocalTime
    -- ^ Chan used to receive clock sync requests. Contains the client's local
    -- time (when the resuest was sent).
    -> IO (ThreadId, IO GlobalTime)
    -- ^ ThreadId of the thread responding to clock sync requests and an IO
    -- function to get the global time. Sine the server's local time is the
    -- global time by definition, this is the same as getLocalTime.
clockSyncServer send recv = do
    threadId <- forkIO $ forever $ do
        sendTimeLocal <- readChan recv
        globalTime <- getLocalTime
        writeChan send (sendTimeLocal, globalTime)
    return (threadId, getLocalTime)

clockSyncClient
    :: Chan LocalTime
    -- ^ Chan used to send clock sync request. Contains the client's local time
    -- (when the resuest was sent).
    -> Chan (LocalTime, GlobalTime)
    -- ^ Chan used to receive responses. Contains the client's local times (when
    -- the request was sent), and the server's (global) time (when it received
    -- the request).
    -> IO (ThreadId, IO GlobalTime)
    -- ^ Return an IO action to get the current (clock synched) game time. Clock
    -- synchronication will start immedietly, but the first call to get the game
    -- time may block untill enough synchronization has been done. This will
    -- continue to perform routine clock synchronization.
clockSyncClient send recv = do
    clockSyncMVar :: MVar ClockSynchronizer <- newEmptyMVar
    -- TODO Swap to UDP this is particularly important for clock
    -- synchronization! In that case we should account for dropped messages
    -- here i.e. send more frequantly to begin with, then after a successful
    -- sync, rever to the usual clockSyncInterval.
    threadId <- do
        -- Send
        _ <- forkIO $ forever $ do
            C.writeChan send =<< getLocalTime
            threadDelay clockSyncInterval
        -- Recv
        do  -- Initial sync
            (sendTimeLocal, timeGlobal) <- readChan recv
            recvTimeLocal <- getLocalTime
            let datum = SyncPoint sendTimeLocal timeGlobal recvTimeLocal
            putMVar clockSyncMVar (mkClockSynchronizer datum)
        forever $ do
            (sendTimeLocal, timeGlobal) <- readChan recv
            recvTimeLocal <- getLocalTime
            let datum = SyncPoint sendTimeLocal timeGlobal recvTimeLocal
            modifyMVar_ clockSyncMVar (return . updateClockSynchronizer datum)

    let getGlobalTime = modifyMVar clockSyncMVar queryGlobalTime

    return (threadId, getGlobalTime)



-- offsetEstimatesToTimeDomainConverter :: EventT LocalTime GlobalTime -> TimeDomainConverter
-- offsetEstimatesToTimeDomainConverter = _

-- timeDomainConverterToGetGlobalTime :: TimeDomainConverter -> (IO (IO GlobalTime))
-- timeDomainConverterToGetGlobalTime = _

-- | Get the current system time in nanoseconds.
getLocalTime :: IO LocalTime
getLocalTime = do
    MkSystemTime s ns <- getSystemTime
    let si  = fromIntegral s
        nsi = fromIntegral ns
    return (si * (10^(9 :: Int)) + nsi)


data ClockSynchronizer = ClockSynchronizer
    { latestPoint :: (LocalTime, GlobalTime)
    -- ^ Last estimated local/global time.
    , driftRate :: Rational
    -- ^ Estimated drift rate (numerator,denominator):
    --          localTimeDelta * driftRate = globalTimeDelta
    -- driftRate > 0
    , offset :: GlobalTime
    -- ^ Estimated offset.
    --          globalTime = (driftRate * localTime) + offset
    , correctionPoint :: (GlobalTime, LocalTime)
    -- ^ Point in time after a updateClockSynchronizer where we aim to get back
    -- on track with the global time. Each component must be strictly greater
    -- than latestPoint.
    , initialPoint :: (LocalTime, GlobalTime)
    -- ^ Initial point used for synchronization. All future corrections to
    -- driftRate and offset will go through this point.
    }

-- | A single data point in synchronization
data SyncPoint
    = SyncPoint
        LocalTime
        -- ^ local time Sync request was sent.
        GlobalTime
        -- ^ global time received in response. We know the global time must
        -- occur between the send and receive time.
        LocalTime
        -- ^ local time Sync request was sent.

-- | Min slope during the correction phase localtime/globaltime
minCorrectionRate :: Rational
minCorrectionRate = 0.1

correctionDuration :: Time
correctionDuration = secondsToTime 1

mkClockSynchronizer :: SyncPoint -> ClockSynchronizer
mkClockSynchronizer (SyncPoint localTimeLo globalTimeMid localTimeHi)
    = ClockSynchronizer
        { latestPoint         = (estLocalTimeMid, globalTimeMid)
        , driftRate           = 1
        , offset              = globalTimeMid - estLocalTimeMid
        , correctionPoint     = (estLocalTimeMid + 1, globalTimeMid + 1)
        , initialPoint        = (estLocalTimeMid, globalTimeMid)
        }
    where
    estLocalTimeMid = round $ (toRational localTimeLo + toRational localTimeHi) / 2


updateClockSynchronizer :: SyncPoint -> ClockSynchronizer -> ClockSynchronizer
updateClockSynchronizer (SyncPoint localTimeLo globalTimeMid localTimeHi) cs
    = ClockSynchronizer
        { latestPoint         = latestPoint cs
        , driftRate           = driftRate'
        , offset              = offset'
        , correctionPoint     = correctionPoint'
        , initialPoint        = initialPoint cs
        }
    where
    (l0, g0) = initialPoint cs
    estLocalTimeMid = (toRational localTimeLo + toRational localTimeHi) / 2
    driftRate' = (toRational globalTimeMid - toRational g0) / (estLocalTimeMid - toRational l0)
    offset' = round $ toRational globalTimeMid - (driftRate' * estLocalTimeMid)
    correctionPoint' = let
        -- Each component must be strictly greater than latestPoint.
        candidateG = queryGlobalTime' driftRate' offset' (fst (latestPoint cs) + correctionDuration)
        candidateGR = toRational candidateG
        candidateSlope = error "TODO updateClockSynchronizer"
        in if candidateSlope < minCorrectionRate
            then error "TODO updateClockSynchronizer"
            else error "TODO updateClockSynchronizer"

queryGlobalTime :: ClockSynchronizer -> IO (ClockSynchronizer, GlobalTime)
queryGlobalTime = error "TODO queryGlobalTime"

queryGlobalTime' :: Rational -> GlobalTime -> LocalTime -> GlobalTime
queryGlobalTime' driftRate' offset' localTime
    = round (driftRate' * toRational localTime) + offset'