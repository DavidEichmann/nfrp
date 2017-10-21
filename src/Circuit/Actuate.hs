{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-orphans #-}

-- | Module to actuate a circuit description
module Circuit.Actuate
  ( ActuatedCircuit
  , Listener(..)
  , Transaction(..)
  , actuate
  , applyTransaction
  , encodeTransaction
  , decodeTransaction
  ) where

import Control.Concurrent (forkIO, threadDelay)
import Control.Concurrent.Async (async, wait)
import qualified Data.Time as Time
import qualified Control.Concurrent.STM as STM
import Control.Monad (forM, forM_, when, unless, forever, void, join)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import Data.Dynamic
import Data.Either (either)
import Data.List (partition)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Serialize
       (Get, Result(..), Serialize(..), decode, encode, runGetPartial,
        runPut)
import qualified Network.Socket as Net
import qualified Network.Socket.ByteString as NetBS
import GHC.Generics

import Circuit.Description hiding (sample)

data ActuatedCircuitInternal node = ActuatedCircuitInternal
  { acListeners :: M.Map GateKey' [Dynamic]
  -- TODO could separate out the circuit state (M.Map GateKey' Dynamic) from the circuit description (M.Map GateKey' (Gate' node))
  --      then the history would be a single circuit description and many states. Unless the circuitry changes!!!!!! Thats future work
  , acHistory :: [(Transaction, Circuit node)] -- ^ update and result (most recent is at the head)
  , acInitialState :: Circuit node -- ^ initial state.
  , acTimeEstimator :: TimeEstimator -- ^ A method to estimate the server time from the local time.
  , acDoOnListenersThread :: IO () -> STM.STM ()
  }

newtype ActuatedCircuit node =
  ActuatedCircuit (STM.TVar (ActuatedCircuitInternal node))

data Listener =
  forall a gateType. (GateValue a) =>
                     Listener (GateKey gateType a)
                              (a -> IO ())

data Transaction =
  Transaction Time.UTCTime
              [GateUpdate]

encodeTransaction :: Transaction -> BS.ByteString
encodeTransaction (Transaction time updates) =
  runPut $ do
    put time
    forM_ updates $ \(GateUpdate key a) -> do
      put key
      put a

decodeTransaction :: Circuit node -> BS.ByteString -> Either String Transaction
decodeTransaction circuit fullStr = do
  (time, updatesStr) <- runGetPartial' (get @Time.UTCTime) fullStr
  updates <- decodeGateUpdates updatesStr
  return (Transaction time updates)
  where
    gateKeys = circuitGateKeysByInt circuit
    decodeGateUpdates :: BS.ByteString -> Either String [GateUpdate]
    decodeGateUpdates str
      | BS.null str = Right []
      | otherwise
        -- Parse gate index
       = do
        (gateInt, str') <- runGetPartial' (get @Int) str
        -- Infer the type, a, by looking up the GateKey' from gateKeys.
        case gateKeys M.! gateInt of
          GateKey' (gateKey :: GateKey gateType a) -> do
            (a, str'') <- runGetPartial' (get :: Get a) str'
            otherUpdates <- decodeGateUpdates str''
            return (GateUpdate gateKey a : otherUpdates)
    runGetPartial' getter str =
      case runGetPartial getter str of
        Fail err _ -> Left $ "Failed to parse a transaction: " ++ err
        Partial _ -> Left "Only managed to partially parse a transaction."
        Done time remainingStr -> Right (time, remainingStr)

-- TODO is there a more optimal way to get a safe buffer size?
--      Could make this much smaller then read further if necessary, but this
--      makes parsing more complicated :-(
recvBufferSize :: Int
recvBufferSize = 4096

acCurrentState :: ActuatedCircuitInternal node -> Circuit node
acCurrentState (ActuatedCircuitInternal _ ((_, currentState):_) _ _ _) =
  currentState
acCurrentState (ActuatedCircuitInternal _ [] currentState _ _) = currentState

data Connection = Connection
  { connTcpSock :: Net.Socket
  , connSockAddr :: Net.SockAddr
  }

actuate ::
     forall node. (Ord node, Bounded node, Serialize node, Show node)
  => M.Map node Net.SockAddr -- ^ map from node to address
  -> node -- ^ what node this is.
  -> Circuit node -- ^ The circuit to actuate
  -> [Listener] -- ^ Listeners the will be called whenever the freshest values (includes roll back values!?).
  -> IO ([GateUpdate] -> IO (), IO ()) -- ^ (Returns the function to perform local transcations, close sockets)
actuate nodeAddresses ownerNode circuit listeners
  = do
  -- See http://www.linuxhowtos.org/C_C++/socket.htm for some networking help.
  -- Open socket
  -- TODO agree on start time? Start actuation on all nodes at the same time.
  -- Connect to other nodes.
  sockets <- connect
  -- Open UDP socket
  socketUDP <- Net.socket Net.AF_INET Net.Datagram 0
  Net.bind
    socketUDP
    (nodeAddresses M.! ownerNode)
  -- start clock sync
  when (ownerNode == minBound) (forkStartClockSyncServer socketUDP)
  forkRequestClockSync ownerNode socketUDP sockets
  initialTimeEstimator <- timeEstimator <$> clockSyncOnce ownerNode socketUDP
  -- initial actuated circuit
  doOnListenersThread <- do
    chan <- STM.newTChanIO
    -- Start listener thread
    void . forkIO . forever . join . STM.atomically . STM.readTChan $ chan
    return (STM.writeTChan chan)
  actuatedCircuitInternalMVar <-
    STM.atomically $ STM.newTVar
      ActuatedCircuitInternal
      { acListeners =
          M.fromListWith
            (++)
            [ (GateKey' key, [toDyn callback])
            | Listener key callback <- listeners
            ]
      , acHistory = []
      , acInitialState = circuit
      , acTimeEstimator = initialTimeEstimator
      , acDoOnListenersThread = doOnListenersThread
      }
  let actuatedCircuit = ActuatedCircuit actuatedCircuitInternalMVar
  -- Continue to receive clock sync messages.
  forkRecvClockSync ownerNode socketUDP actuatedCircuitInternalMVar
  -- Create the transaction function.
  let performTransaction = applyTransaction actuatedCircuit
  -- Start threads that listens to other nodes and injects transactions
  sequence_
    . fmap forkIO
    . M.mapWithKey (\remoteNode conn -> listenForRemoteTransactions
                                            (STM.atomically . performTransaction)
                                            remoteNode
                                            (connTcpSock conn))
    $ sockets
  -- Listen for circuit transactions from the given node via the given socket.
  return
    ( \gateUpdates
        -> do
          -- Get current time.
          localTime <- Time.getCurrentTime
          transaction <- STM.atomically $ do
            acCircuit <- STM.readTVar actuatedCircuitInternalMVar
            -- Get the estimated server time.
            let (estimatedTime, newTimeEstimator)
                  = estimateTime
                    (acTimeEstimator acCircuit)
                    localTime
            -- perform the transaction.
            STM.writeTVar actuatedCircuitInternalMVar acCircuit {
              acTimeEstimator = newTimeEstimator
            }
            let transaction = Transaction estimatedTime gateUpdates
            performTransaction transaction
            return transaction
          -- broadcast the transaction.
          forM_ sockets $ \conn ->
            NetBS.send (connTcpSock conn) (encodeTransaction transaction)

    , mapM_ (Net.close . connTcpSock) sockets
    )
  where
    listenForRemoteTransactions ::
         (Transaction -> IO ()) -> node -> Net.Socket -> IO ()
    listenForRemoteTransactions performTransaction node socket = loop
      where
        loop
        -- TODO use _node?
         = do
          msg <- NetBS.recv socket recvBufferSize
          let connectionClosed = BS.null msg
          unless connectionClosed $ do
            let transactionOrErr = decodeTransaction circuit msg
            either
              (\errorMsg -> do
                 putStrLn
                   ("Failed to decode transaction from \"" ++ show node ++ "\":")
                 putStrLn ("Error Message: " ++ errorMsg)
                 putStr "Data: "
                 BS8.putStrLn msg)
              performTransaction
              transactionOrErr
            loop
    -- |Connect to all other nodes. Returns a map from nodes (excluding ownerNode)
    -- to a Socket (TCP, UDP, SocketAddr) used to comunicate with the node.
    connect :: IO (M.Map node Connection)
    connect = do
      putStrLn ("Actuating as a \"" ++ show ownerNode ++ "\" node.")
      let ownerSockAddr = nodeAddresses M.! ownerNode
      putStrLn $ "Opening TCP port: " ++ show ownerSockAddr
      socket <- Net.socket Net.AF_INET Net.Stream 0
      Net.bind socket ownerSockAddr
      Net.listen socket 5
      -- Accept connection to designated socket from greater nodes.
      putStrLn "Connecting to remote nodes..."
      let (lesserNodes, greaterNodes) =
            partition (< ownerNode) . filter (/= ownerNode) $
            M.keys nodeAddresses
      let greaterNodesCount = length greaterNodes
      greaterSocketsMapAssocsAsync <-
        async $
        forM [1 .. greaterNodesCount] $ \_
         -> do
           -- Accept connection.
          (remoteSocket, remoteSocketAddr) <- Net.accept socket
          -- Read remote node type
          (remoteNode :: node) <-
            either
              (\str ->
                 error ("Failed to parse node type from remote node: " ++ str))
              id .
            decode <$>
            NetBS.recv remoteSocket recvBufferSize :: IO node
          return
            ( remoteNode
            , Connection
              { connTcpSock  = remoteSocket
              , connSockAddr = remoteSocketAddr
              }
            )
          -- Connect to all lesser nodes
      lesserSocketsMapAssocsAsyncs <-
        forM lesserNodes $ \remoteNode
        -- Connect to remote node.
         ->
          async $ do
            let remoteSockAddr = nodeAddresses M.! remoteNode
            remoteSocket <- Net.socket Net.AF_INET Net.Stream 0
            Net.connect remoteSocket remoteSockAddr
            -- Send owner node type.
            _bytesSent <- NetBS.send remoteSocket (encode ownerNode)
            return
              ( remoteNode
              , Connection
                { connTcpSock  = remoteSocket
                , connSockAddr = remoteSockAddr
                }
              )
      -- Wait for connections to be established.
      greaterSocketsMapAssocs <- wait greaterSocketsMapAssocsAsync
      lesserSocketsMapAssocs <- mapM wait lesserSocketsMapAssocsAsyncs
      let remoteSockets =
            M.fromList (lesserSocketsMapAssocs ++ greaterSocketsMapAssocs)
      putStrLn "Connection established."
      return remoteSockets

-- |Apply the transaction (with possible rollback and replay), updating the internal
-- state and calling listeners.
applyTransaction :: forall node. ActuatedCircuit node -> Transaction -> STM.STM ()
applyTransaction (ActuatedCircuit aCircuitMV) transaction@(Transaction time updates) = do
  newCircuit <- applyTransaction' =<< STM.readTVar aCircuitMV
  STM.writeTVar aCircuitMV newCircuit
  where
    applyTransaction' ::
         ActuatedCircuitInternal node -> STM.STM (ActuatedCircuitInternal node)
    applyTransaction' actuatedCircuitInternal = do
      let transactions = acHistory actuatedCircuitInternal
      let latestTimeMay =
            case transactions of
              [] -> Nothing
              (Transaction t _, _):_ -> Just t
      case fromMaybe GT (compare time <$> latestTimeMay) of
        LT -> error "TODO roll back and replay circuit."
        EQ ->
          error $
          "TODO Cannot currently apply multiple transactions at the same time." ++
          "Need a way to resolve order that is unambiguous accross nodes."
        GT
          -- Get the next cifcuit state.
         -> do
          let (newCircuit, behaviorUpdates, events) =
                applyUpdates (acCurrentState actuatedCircuitInternal) updates
          -- Call behavior/event listeners.
          let callListeners changes =
                forM_ (M.assocs changes) $ \(key', valDyn) ->
                  case M.lookup key' (acListeners actuatedCircuitInternal) of
                    Nothing -> return ()
                    Just listeners ->
                      forM_ listeners $ \listener ->
                        fromDyn
                          (dynApp listener valDyn)
                          (error "Expected listener of type \"a -> IO ()\"") :: IO ()
          acDoOnListenersThread actuatedCircuitInternal $ do
            callListeners behaviorUpdates
            callListeners events
          -- Define the new states by setting the affected states
          return
            ActuatedCircuitInternal
            { acListeners = acListeners actuatedCircuitInternal
            , acHistory = (transaction, newCircuit) : transactions
            , acInitialState = acInitialState actuatedCircuitInternal
            , acTimeEstimator = acTimeEstimator actuatedCircuitInternal
            , acDoOnListenersThread = acDoOnListenersThread actuatedCircuitInternal
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
  | SNTPResponse Time.UTCTime Time.UTCTime
  deriving (Generic, Serialize, Show)

clockSyncIntervalMicroS :: Int
clockSyncIntervalMicroS = 1000000

forkStartClockSyncServer
  :: Net.Socket
  -> IO ()
forkStartClockSyncServer udpSocket = void . forkIO . forever $ do
    -- Listen and respond to SNTPRequests.
    (recvStr, clientSockAddr) <- NetBS.recvFrom udpSocket recvBufferSize
    -- Note the receive time.
    serverRecvTime <- Time.getCurrentTime
    -- Decode the message.
    let SNTPRequest clientSendTime = either error id (decode recvStr)
    -- Respond.
    let response = SNTPResponse clientSendTime serverRecvTime
    NetBS.sendTo udpSocket (encode response) clientSockAddr

clockSyncOnce
  :: (Eq node, Bounded node)
  => node
  -> Net.Socket
  -> IO (Time.UTCTime, Time.UTCTime)
clockSyncOnce ownerNode udpSocket
  | ownerNode == minBound = do
    serverTime <- Time.getCurrentTime
    return (serverTime, serverTime)
  | otherwise = recvClockSyncOnce udpSocket

recvClockSyncOnce
  :: Net.Socket
  -> IO (Time.UTCTime, Time.UTCTime)
recvClockSyncOnce udpSocket = do
  -- Receive response
  putStrLn "Waiting for Clock Sync..."
  (responseStr, _recvSockAddr) <- NetBS.recvFrom udpSocket recvBufferSize
  -- Note the response time.
  clientRecvTime <- Time.getCurrentTime
  -- Decode the message. Expect a valid SNTPResponse from the server.
  let SNTPResponse clientSendTime serverRecvTime = either error id (decode responseStr)
  -- update the circuit
  let
    pingTime = clientRecvTime `Time.diffUTCTime` clientSendTime
    estimatedTransmitionDelay = pingTime / 2
    estimatedTime = estimatedTransmitionDelay `Time.addUTCTime` serverRecvTime
  -- Debug output
  let
    pingMs = (realToFrac pingTime :: Double) * 1000
    offsetMs = (realToFrac (estimatedTime `Time.diffUTCTime` clientRecvTime) :: Double) * 1000
  putStrLn $ "Clock Sync received."
           ++ "\n\tPing:   " ++ show pingMs
           ++ "\n\tOffset: " ++ show offsetMs
  return (clientRecvTime, estimatedTime)

forkRecvClockSync
  :: (Ord node, Bounded node)
  => node
  -> Net.Socket
  -> STM.TVar (ActuatedCircuitInternal node)
  -> IO ()
forkRecvClockSync ownerNode udpSocket circuitMVar
  -- Server doesn't need to sync.
  | ownerNode == serverNode = return ()
  -- Client
  | otherwise = void . forkIO . forever $ do
      -- Receive response
      sample <- recvClockSyncOnce udpSocket
      STM.atomically . STM.modifyTVar circuitMVar $ \circuit ->
        circuit {
          acTimeEstimator = setLatestSample (acTimeEstimator circuit) sample
        }
  where
    serverNode = minBound

requestClockSyncOnce
  :: Net.Socket
  -> Net.SockAddr
  -> IO ()
requestClockSyncOnce udpSocket serverSockAddr = do
  -- Note the send time.
  clientSendTime <- Time.getCurrentTime
  -- Send the request.
  let request = SNTPRequest clientSendTime
  _ <- NetBS.sendTo udpSocket (encode request) serverSockAddr
  return ()

forkRequestClockSync
  :: (Ord node, Bounded node)
  => node
  -> Net.Socket
  -> M.Map node Connection
  -> IO ()
forkRequestClockSync ownerNode udpSocket sockets
  -- Server doesn't need to sync.
  | ownerNode == serverNode = return ()
  -- Client
  | otherwise = let
    serverConn = sockets M.! serverNode
    serverSockAddr = connSockAddr serverConn
    in void . forkIO . forever $ do
      -- Send SNTPRequests.
      requestClockSyncOnce udpSocket serverSockAddr
      -- Wait
      threadDelay clockSyncIntervalMicroS
  where
    serverNode = minBound


-- TODO a more sufisticated clock estimator! Perhaps estimate clock drift.
-- | Time Estimator assumes that:
--      localClock = serverClock + offset
-- where offset is constant
data TimeEstimator
  = TimeEstimator
    (Time.UTCTime, Time.UTCTime) -- ^ latest sample used to adjust current estimate.
    [(Time.UTCTime, Time.UTCTime)]       -- ^ Committed (local, estimated server time) samples, latest at head. All estimates before and equal the head local time are fixed.

timeEstimator :: (Time.UTCTime, Time.UTCTime) -> TimeEstimator
timeEstimator initialSample = TimeEstimator initialSample []

-- | Minimum rate of clock (server clock rate / client clock rate) during syncCorrectionTime
minSyncRate :: Time.NominalDiffTime
minSyncRate = 0.5

-- | Maximum rate of clock (server clock rate / client clock rate) during syncCorrectionTime
maxSyncRate :: Time.NominalDiffTime
maxSyncRate = 2

-- | Estimate server time from client time and fix to that time
estimateTime :: TimeEstimator -> Time.UTCTime -> (Time.UTCTime, TimeEstimator)
estimateTime (TimeEstimator latestSample []) local = let
  estimate = estimateTimeSimple latestSample local
  in (estimate, TimeEstimator latestSample [(local, estimate)])
estimateTime te@(TimeEstimator latestSample commited@(commit0@(local0, estimate0) : commitedRest)) local
  | local == local0 = (estimate0, te)
  -- time is before latest fixed time
  | local < local0 = let
    estimate = estimateTimeFromCommited local (local0, estimate0) commitedRest
    in (estimate, TimeEstimator latestSample ((local, estimate) : commited))
  -- time is after latest fixed time. Estimate, smooth, and commit
  | otherwise = let
    sampleEstimateTime = estimateTimeSimple latestSample local
    commitEstimateTime = estimateTimeSimple commit0 local
    estimateFromCommitAWithRate rate = ((local `Time.diffUTCTime` local0) * rate) `Time.addUTCTime` estimate0
    estimate = if commitEstimateTime < sampleEstimateTime
      -- If behind, then move at maxSyncRate till synched
      then min sampleEstimateTime (estimateFromCommitAWithRate maxSyncRate)
      -- Else move at minSyncRate till synched
      else max sampleEstimateTime (estimateFromCommitAWithRate minSyncRate)
    -- Get rate
    -- correctionTargetLocalTime = syncCorrectionTime `Time.addUTCTime` localSample
    -- correctionTargetEstimateTime = estimateTimeSimple latestSample correctionTargetLocalTime
    -- unclampedCorrectionRate = (correctionTargetEstimateTime `Time.diffUTCTime` estimate0) / syncCorrectionTime
    -- correctionRate = max minSyncRate (min unclampedCorrectionRate maxSyncRate)
    -- -- find time at which synch is achieved. a rate of 1 is used after this point.
    -- syncAchievedLocalTime =
    in (estimate , TimeEstimator latestSample ((local, estimate) : commited))


estimateTimeFromCommited :: Time.UTCTime -> (Time.UTCTime, Time.UTCTime) -> [(Time.UTCTime, Time.UTCTime)] -> Time.UTCTime
estimateTimeFromCommited local commitA [] = estimateTimeSimple commitA local
estimateTimeFromCommited local (localB, estimateB) (commitA@(localA, estimateA) : commits)
  | localA == local  = estimateA
  | localA > local   = estimateTimeFromCommited local commitA commits
  | localB < local   = error "estimateTimeFromCommited expects local to be within or before the committed estimates"
  | otherwise        = let
    dEstimatePerDLocal  = (estimateB `Time.diffUTCTime` estimateA) / (localB `Time.diffUTCTime` localA)
    localTimePastA = local `Time.diffUTCTime` localA
    in (dEstimatePerDLocal * localTimePastA) `Time.addUTCTime` estimateA

estimateTimeSimple :: (Time.UTCTime, Time.UTCTime) -> Time.UTCTime -> Time.UTCTime
estimateTimeSimple (local0, server0) local = let
  offset = local0 `Time.diffUTCTime` server0
  in (negate offset) `Time.addUTCTime` local

setLatestSample :: TimeEstimator -> (Time.UTCTime, Time.UTCTime) -> TimeEstimator
setLatestSample (TimeEstimator _ commited) sample = TimeEstimator sample commited
