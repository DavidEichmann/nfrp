{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Module to actuate a circuit description
module Circuit.Net
  ( Connection(..)
  , baseNfrpPort
  , recvBufferSize
  , clockSyncOnce
  , forkRequestClockSync
  , forkRecvClockSync
  , forkStartClockSyncServer
  ) where

import Circuit.ClockSync
import Control.Concurrent (forkIO, threadDelay)
import qualified Control.Concurrent.STM as STM
import Control.Monad (forever, void)
import Data.Either (either)
import qualified Data.Map as M
import Data.Serialize (Serialize(..), decode, encode)
import qualified Data.Time as Time
import GHC.Generics
import qualified Network.Socket as Net
import qualified Network.Socket.ByteString as NetBS

baseNfrpPort :: Int
baseNfrpPort = 23789

-- TODO is there a more optimal way to get a safe buffer size?
--      Could make this much smaller then read further if necessary, but this
--      makes parsing more complicated :-(
recvBufferSize :: Int
recvBufferSize = 4096

data Connection = Connection
  { connTcpSock :: Net.Socket
  , connSockAddr :: Net.SockAddr
  }

deriving instance Generic Time.Day

instance Serialize Time.Day

instance Serialize Time.DiffTime where
  put = put . Time.diffTimeToPicoseconds
  get = Time.picosecondsToDiffTime <$> get

deriving instance Generic Time.UTCTime

instance Serialize Time.UTCTime

data UdpMessage
  = SNTPRequest Time.UTCTime
  | SNTPResponse Time.UTCTime
                 Time.UTCTime
  deriving (Generic, Serialize, Show)

clockSyncIntervalMicroS :: Int
clockSyncIntervalMicroS = 1000000

forkStartClockSyncServer :: Net.Socket -> IO ()
forkStartClockSyncServer udpSocket =
  void . forkIO . forever $
    -- Listen and respond to SNTPRequests.
   do
    (recvStr, clientSockAddr) <- NetBS.recvFrom udpSocket recvBufferSize
    -- Note the receive time.
    serverRecvTime <- Time.getCurrentTime
    -- Decode the message.
    let SNTPRequest clientSendTime = either error id (decode recvStr)
    -- Respond.
    let response = SNTPResponse clientSendTime serverRecvTime
    NetBS.sendTo udpSocket (encode response) clientSockAddr

clockSyncOnce ::
     (Eq node, Bounded node)
  => node
  -> Net.Socket
  -> IO (Time.UTCTime, Time.UTCTime)
clockSyncOnce ownerNode udpSocket
  | ownerNode == minBound = do
    serverTime <- Time.getCurrentTime
    return (serverTime, serverTime)
  | otherwise = recvClockSyncOnce udpSocket

recvClockSyncOnce :: Net.Socket -> IO (Time.UTCTime, Time.UTCTime)
recvClockSyncOnce udpSocket
  -- Receive response
  -- putStrLn "Waiting for Clock Sync..."
 = do
  (responseStr, _recvSockAddr) <- NetBS.recvFrom udpSocket recvBufferSize
  -- Note the response time.
  clientRecvTime <- Time.getCurrentTime
  -- Decode the message. Expect a valid SNTPResponse from the server.
  let SNTPResponse clientSendTime serverRecvTime =
        either error id (decode responseStr)
  -- update the circuit
  let pingTime = clientRecvTime `Time.diffUTCTime` clientSendTime
      estimatedTransmitionDelay = pingTime / 2
      estimatedTime = estimatedTransmitionDelay `Time.addUTCTime` serverRecvTime
  -- Debug output
  -- let
  --   pingMs = (realToFrac pingTime :: Double) * 1000
  --   offsetMs = (realToFrac (estimatedTime `Time.diffUTCTime` clientRecvTime) :: Double) * 1000
  -- putStrLn $ "Clock Sync received."
  --          ++ "\n\tPing:   " ++ show pingMs
  --          ++ "\n\tOffset: " ++ show offsetMs
  return (clientRecvTime, estimatedTime)

forkRecvClockSync ::
     (TimeEstimator te, Ord node, Bounded node)
  => node
  -> Net.Socket
  -> STM.TVar a
  -> (a -> te)
  -> (a -> te -> a)
  -> IO ()
forkRecvClockSync ownerNode udpSocket aMVar getTE setTE
  -- Server doesn't need to sync.
  | ownerNode == serverNode = return ()
  -- Client
  | otherwise =
    void . forkIO . forever $
      -- Receive response
     do
      sample <- recvClockSyncOnce udpSocket
      STM.atomically . STM.modifyTVar aMVar $ \a ->
        setTE a (setLatestSample (getTE a) sample)
  where
    serverNode = minBound

requestClockSyncOnce :: Net.Socket -> Net.SockAddr -> IO ()
requestClockSyncOnce udpSocket serverSockAddr
  -- Note the send time.
 = do
  clientSendTime <- Time.getCurrentTime
  -- Send the request.
  let request = SNTPRequest clientSendTime
  _ <- NetBS.sendTo udpSocket (encode request) serverSockAddr
  return ()

forkRequestClockSync ::
     (Ord node, Bounded node)
  => node
  -> Net.Socket
  -> M.Map node Connection
  -> IO ()
forkRequestClockSync ownerNode udpSocket sockets
  -- Server doesn't need to sync.
  | ownerNode == serverNode = return ()
  -- Client
  | otherwise =
    let serverConn = sockets M.! serverNode
        serverSockAddr = connSockAddr serverConn
    in void . forkIO . forever $
      -- Send SNTPRequests.
        do
         requestClockSyncOnce udpSocket serverSockAddr
      -- Wait
         threadDelay clockSyncIntervalMicroS
  where
    serverNode = minBound
