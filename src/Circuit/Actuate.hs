{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
import Control.Exception (assert)
import qualified Data.Time as Time
import Data.Word
import qualified Control.Concurrent.MVar as MV
import Control.Monad (forM, forM_, unless, forever)
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

import Circuit.Description

type Time = Word64

-- | returns time in microseconds
getElapsedTimeMicroS :: Time.UTCTime -> IO Time
getElapsedTimeMicroS startTime = do
  t <- Time.getCurrentTime
  return (round ((t `Time.diffUTCTime` startTime) * 1000000))


data ActuatedCircuitInternal node = ActuatedCircuitInternal
  { acListeners :: M.Map GateKey' [Dynamic]
  -- TODO could separate out the circuit state (M.Map GateKey' Dynamic) from the circuit description (M.Map GateKey' (Gate' node))
  --      then the history would be a single circuit description and many states. Unless the circuitry changes!!!!!! Thats future work
  , acHistory :: [(Transaction, Circuit node)] -- ^ update and result (most recent is at the head)
  , acInitialState :: Circuit node -- ^ initial state.
  , acClockSync :: Time -> Time -- ^ A method to estimate the global time from the local time.
  }

newtype ActuatedCircuit node =
  ActuatedCircuit (MV.MVar (ActuatedCircuitInternal node))

data Listener =
  forall a gateType. (GateValue a) =>
                     Listener (GateKey gateType a)
                              (a -> IO ())

data Transaction =
  Transaction Time
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
  (time, updatesStr) <- runGetPartial' (get @Time) fullStr
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
acCurrentState (ActuatedCircuitInternal _ ((_, currentState):_) _ _) =
  currentState
acCurrentState (ActuatedCircuitInternal _ [] currentState _) = currentState

data Connection = Connection
  { connTcpSock :: Net.Socket
  , connSockAddr :: Net.SockAddr
  }

actuate ::
     forall node. (Ord node, Bounded node, Serialize node, Show node)
  => M.Map node Int -- ^ map from node to port number (TODO and IP address)
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
  -- initial actuated circuit
  initialClockSync <- clockSyncOnce ownerNode sockets
  actuatedCircuitInternalMVar <-
    MV.newMVar
      ActuatedCircuitInternal
      { acListeners =
          M.fromListWith
            (++)
            [ (GateKey' key, [toDyn callback])
            | Listener key callback <- listeners
            ]
      , acHistory = []
      , acInitialState = circuit
      , acClockSync = initialClockSync
      }
  let actuatedCircuit = ActuatedCircuit actuatedCircuitInternalMVar
  -- Start clock sync thread
  -- TODO this thread should stop gracefully.
  forkIO (clockSync ownerNode sockets actuatedCircuitInternalMVar)
  -- Create the transaction function.
  let performTransaction = applyTransaction actuatedCircuit
  -- Start threads that listens to other nodes and injects transactions
  sequence_
    . fmap forkIO
    . M.mapWithKey (\remoteNode conn -> listenForRemoteTransactions
                                            performTransaction
                                            remoteNode
                                            (connTcpSock conn))
    $ sockets
  -- Get start time
  startTime <- Time.getCurrentTime
  -- Listen for circuit transactions from the given node via the given socket.
  return
    ( \gateUpdates
        -> do
          -- TODO account for drift in different node's clocks
          -- Get current time and time since start.
          timeElapsed <- getElapsedTimeMicroS startTime
          -- perform the transaction.
          let transaction = Transaction timeElapsed gateUpdates
          performTransaction transaction
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
      let ownerPort = fromIntegral (nodeAddresses M.! ownerNode)
      let ownerSockAddr =
            Net.SockAddrInet ownerPort (Net.tupleToHostAddress (127, 0, 0, 1))
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
          remoteSocketUDP <- Net.socket Net.AF_INET Net.Datagram 0
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
            let remotePort = fromIntegral (nodeAddresses M.! remoteNode)
            let remoteSockAddr =
                  Net.SockAddrInet
                    remotePort
                    (Net.tupleToHostAddress (127, 0, 0, 1))
            remoteSocket    <- Net.socket Net.AF_INET Net.Stream   0
            remoteSocketUDP <- Net.socket Net.AF_INET Net.Datagram 0
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
applyTransaction :: forall node. ActuatedCircuit node -> Transaction -> IO ()
applyTransaction (ActuatedCircuit aCircuitMV) transaction@(Transaction time updates) =
  MV.modifyMVar_ aCircuitMV applyTransaction'
  where
    applyTransaction' ::
         ActuatedCircuitInternal node -> IO (ActuatedCircuitInternal node)
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
          callListeners behaviorUpdates
          callListeners events
          -- Define the new states by setting the affected states
          return
            ActuatedCircuitInternal
            { acListeners = acListeners actuatedCircuitInternal
            , acHistory = (transaction, newCircuit) : transactions
            , acInitialState = acInitialState actuatedCircuitInternal
            , acClockSync = acClockSync actuatedCircuitInternal
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

clockSyncOnce
  :: Bounded node
  => node
  -> Net.Socket
  -> M.Map node Connection
  -> IO (Time -> Time)
clockSyncOnce ownerNode udpSocket sockets = undefined

clockSync
  :: (Ord node, Bounded node)
  => node
  -> Net.Socket
  -> M.Map node Connection
  -> MV.MVar (ActuatedCircuitInternal node)
  -> IO ()
clockSync ownerNode udpSocket sockets circuitMVar
  -- Server
  | ownerNode == serverNode = forever $ do
    -- Listen and respond to SNTPRequests.
    (recvStr, clientSockAddr) <- NetBS.recvFrom udpSocket recvBufferSize
    -- Note the receive time.
    serverRecvTime <- Time.getCurrentTime
    -- Decode the message.
    let SNTPRequest clientSendTime = either error id (decode recvStr)
    -- Respond.
    let response = SNTPResponse clientSendTime serverRecvTime
    NetBS.sendTo udpSocket (encode response) clientSockAddr
  -- Client
  | otherwise = do
    let
      serverConn = sockets M.! serverNode
      serverSockAddr = connSockAddr serverConn
    -- Periodically send SNTPRequests.
    forkIO . forever $ do
      -- Note the send time.
      clientSendTime <- Time.getCurrentTime
      -- Send the request.
      let request = SNTPRequest clientSendTime
      NetBS.sendTo udpSocket (encode request) serverSockAddr
      -- Wait
      threadDelay clockSyncIntervalMicroS
    -- listen for SNTPResponses
    forever $ do
      -- Receive response
      (responseStr, recvSockAddr) <- NetBS.recvFrom udpSocket recvBufferSize
      -- Note the response time.
      clientRecvTime <- Time.getCurrentTime
      -- Decode the message. Expect a valid SNTPResponse from the server.
      let SNTPResponse clientSendTime serverRecvTime = either error id (decode responseStr)
      -- update the circuit
      let
        pingTime = clientRecvTime `Time.diffUTCTime` clientSendTime
        estimatedTransmitionDelay = pingTime / 2
        estimatedTime = estimatedTransmitionDelay `Time.addUTCTime` serverRecvTime
      MV.modifyMVar_ circuitMVar $ \circuit -> do


        error "Update the clock estimator!"


  where
    serverNode = minBound


-- TODO a more sufisticated clock estimator! Perhaps estimate clock drift.
-- | Time Estimator assumes that:
--      localClock = serverClock + offset
-- where offset is constant
data TimeEstimator
  = TimeEstimator
    (Maybe (Time.UTCTime, Time.UTCTime)) -- ^ latest sample used to adjust current estimate.
    [(Time.UTCTime, Time.UTCTime)]       -- ^ Committed (local, estimated server time) samples, latest at head. All estimates before and equal the head local time are fixed.

emptyTimeEstimator :: TimeEstimator
emptyTimeEstimator = TimeEstimator Nothing []

-- | The ammount of time in which to attempt to smoothy synchronize to the server's time.
syncCorrectionTime :: Time.NominalDiffTime
syncCorrectionTime = Time.picosecondsToDiffTime (fromIntegral clockSyncIntervalMicroS * 1000000000)

-- | Minimum rate of clock (server clock rate / client clock rate) during syncCorrectionTime
minSyncRate :: Time.NominalDiffTime
minSyncRate = 0.5

-- | Maximum rate of clock (server clock rate / client clock rate) during syncCorrectionTime
maxSyncRate :: Time.NominalDiffTime
maxSyncRate = 2

-- | Estimate server time from client time and fix to that time
estimateTime :: TimeEstimator -> Time.UTCTime -> (Time.UTCTime, TimeEstimator)
estimateTime (TimeEstimator Nothing []) localTime = let
  estimate = 0
  in (estimate, TimeEstimator Nothing [(localTime, estimate)])
estimateTime (TimeEstimator (Just latestSample) []) localTime = let
  estimate = estimateTimeSimple latestSample localTime
  in (estimate, TimeEstimator (Just latestSample) [(localTime, estimate)])
estimateTime te@(TimeEstimator latestSampleMay commited@((local0, server0) : _)) local
  | local == local0 = (server0, te)
  -- time is before latest fixed time
  | local < local0 = let
    estimateTimeFromCommited = TODO
    in (estimateTimeFromCommited commited, te)
  -- time is aftter latest fixed time. Estimate, smooth, and commit
  | otherwise = let
    estimate = TODO
    in (estimate , TimeEstimator latestSampleMay ((local, estimate) : commited))

estimateTimeSimple :: (Time.UTCTime, Time.UTCTime) -> Time.UTCTime -> Time.UTCTime
estimateTimeSimple (local0, server0) local = let
  offset = local0 `Time.diffUTCTime` server0
  in (negate offset) `Time.addUTCTime` local

addSample :: TimeEstimator -> (Time.UTCTime, Time.UTCTime) -> TimeEstimator
addSample (TimeEstimator _ commited) sample = TimeEstimator (Just sample) commited
