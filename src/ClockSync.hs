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
    ( -- clockSyncServer
    -- , clockSyncClient
     getLocalTime
    ) where

import           Data.Binary (Binary)
import           Control.Applicative
import           Control.Concurrent
import           Control.Concurrent.STM
import qualified Control.Concurrent.Chan as C
import           Control.DeepSeq
import           Control.Monad (forever, forM_)
import           Data.Either (partitionEithers)
import           Data.IORef
import           Data.List (group, intercalate, partition)
import           Data.Maybe (catMaybes, fromJust, fromMaybe, mapMaybe)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Time.Clock.System (SystemTime(..), getSystemTime)
import           GHC.Generics (Generic)

import FRP
import Time
import TimeSpan

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

-- clockSyncServer
--     :: _
--     -> IO (ThreadId, IO GlobalTime)
-- clockSyncServer = _

-- clockSyncClient
--     :: _
--     -> IO (ThreadId, IO GlobalTime)
--     -- ^ Return an IO action to get the current (clock synched) game time. Clock
--     -- synchronication will start immedietly, but the first call to get the game
--     -- time may block untill enough synchronization has been done. This will
--     -- continue to perform routine clock synchronization.
-- clockSyncClient = _

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


-- data ClockSynchronizer
--     -- | Doing initial synchronization
--     = InitialSync
--     -- | Synchronized.
--     | Synched
--         { t0L :: LocalTime
--         -- ^ local time where we last synchronized
--         , t0GOld :: GlobalTime
--         -- ^ old estimated global time where we last synchronized
--         , t0GNew :: GlobalTime
--         -- ^ new estimated global time where we last synchronized
--         , driftRate :: (GlobalTime, LocalTime)
--         -- ^ Estimated drift rate (numerator,denominator):
--         --          localTimeDelta * driftRate = GlobalTimeDelta
--         -- driftRate > 0
--         , correctionDuration :: LocalTime
--         -- ^ Duration of time (after the last sync time) for which the clock
--         -- will be speed up / slowed down to correct for the the offset between
--         }


-- -- | A single data point in synchronization
-- data SynchPoint
--     = SyncPoint
--         LocalTime
--         -- ^ local time Sync request was sent.
--         GlobalTime
--         -- ^ global time received in response. We know the global time must
--         -- occur between the send and receive time.
--         LocalTime
--         -- ^ local time Sync request was sent.