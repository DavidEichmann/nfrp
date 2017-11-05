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
  , baseNfrpPort
  ) where

import Circuit.ClockSync
import Circuit.Net
import Control.Concurrent (forkIO, threadDelay)
import Control.Concurrent.Async (async, wait)
import qualified Control.Concurrent.STM as STM
import Control.Exception (IOException, catch)
import Control.Monad
       (forM, forM_, forever, join, unless, void, when)
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
import qualified Data.Set as S
import qualified Data.Time as Time
import qualified Network.Socket as Net
import qualified Network.Socket.ByteString as NetBS

import Circuit.Description hiding (sample)

-- ^ (update, result, changed gates) (most recent is at the head)
type HistoryD node = (Transaction, Circuit node, S.Set GateKey')

-- ^ (history deltas (most recent is at the head), initial state)
type History node = ([HistoryD node], Circuit node)

histCurrent :: History node -> Circuit node
histCurrent (deltas, initialState) =
  case deltas of
    [] -> initialState
    (_, current, _):_ -> current

-- TODO support splitting when equal times.... need some way to unambiguously resolve
-- order of transactions!!!
histSplit :: Time.UTCTime -> History node -> ([HistoryD node], History node)
histSplit time (deltas, initialState) =
  case deltas of
    [] -> ([], ([], initialState))
    currentDelta@(Transaction currentTime _, _, _):prevDeltas ->
      case currentTime `compare` time of
        EQ ->
          error
            "need some way to unambiguously resolve order of transactions!!!"
        LT -> ([], (deltas, initialState))
        GT ->
          let (splitDeltas', splitHist) =
                histSplit time (prevDeltas, initialState)
          in (currentDelta : splitDeltas', splitHist)

data ActuatedCircuitInternal node = ActuatedCircuitInternal
  { acListeners :: M.Map GateKey' [Dynamic]
  -- TODO could separate out the circuit state (M.Map GateKey' Dynamic) from the circuit description (M.Map GateKey' (Gate' node))
  --      then the history would be a single circuit description and many states. Unless the circuitry changes!!!!!! Thats future work
  , acHistory :: History node
  , acTimeEstimator :: SimpleTimeEstimator -- ^ A method to estimate the server time from the local time.
  , acDoOnListenersThread :: IO () -> STM.STM ()
  }

newtype ActuatedCircuit node =
  ActuatedCircuit (STM.TVar (ActuatedCircuitInternal node))

data Listener =
  forall a. (GateValue a
                     -- A listener that is called whenever the underlying value has changed.
                     -- On rollback, this will be called with the newest value if any of the
                     -- rolled back transaction or the new transactions affected the
                     -- underlying behavior.
             ) =>
            Setter (GateKey 'BehaviorGate a)
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

actuate ::
     forall node. (Ord node, Bounded node, Serialize node, Show node)
  => M.Map node (Net.HostName, Int) -- ^ map from node to address info
  -> node -- ^ what node this is.
  -> Circuit node -- ^ The circuit to actuate
  -> [Listener] -- ^ Listeners the will be called whenever the freshest values (includes roll back values!?).
  -> IO ([GateUpdate] -> IO (), IO ()) -- ^ (Returns the function to perform local transcations, close sockets)
actuate hostNamesAndPorts ownerNode circuit listeners
  -- See http://www.linuxhowtos.org/C_C++/socket.htm for some networking help.
  -- Open socket
  -- TODO agree on start time? Start actuation on all nodes at the same time.
  -- Connect to other nodes.
 = do
  sockets <- connect
  -- Open UDP socket
  udpPortInfo <-
    head <$>
    Net.getAddrInfo
      (Just (Net.defaultHints {Net.addrFlags = [Net.AI_PASSIVE]}))
      Nothing
      (Just (show ownerNodePort))
  socketUDP <- Net.socket (Net.addrFamily udpPortInfo) Net.Datagram 0
  Net.bind socketUDP (Net.addrAddress udpPortInfo)
  -- start clock sync
  when (ownerNode == minBound) (forkStartClockSyncServer socketUDP)
  forkRequestClockSync ownerNode socketUDP sockets
  initialTimeEstimator <-
    simpleTimeEstimator <$> clockSyncOnce ownerNode socketUDP
  -- initial actuated circuit
  doOnListenersThread <-
    do chan <- STM.newTChanIO
    -- Start listener thread
       void . forkIO . forever . join . STM.atomically . STM.readTChan $ chan
       return (STM.writeTChan chan)
  actuatedCircuitInternalMVar <-
    STM.atomically $
    STM.newTVar
      ActuatedCircuitInternal
      { acListeners =
          M.fromListWith
            (++)
            [ (GateKey' key, [toDyn callback])
            | Setter key callback <- listeners
            ]
      , acHistory = ([], circuit)
      , acTimeEstimator = initialTimeEstimator
      , acDoOnListenersThread = doOnListenersThread
      }
  let actuatedCircuit = ActuatedCircuit actuatedCircuitInternalMVar
  -- Continue to receive clock sync messages.
  forkRecvClockSync
    ownerNode
    socketUDP
    actuatedCircuitInternalMVar
    acTimeEstimator
    (\circuitInternal newTimeEstimator ->
       circuitInternal {acTimeEstimator = newTimeEstimator})
  -- Create the transaction function.
  let performTransaction = applyTransaction actuatedCircuit
  -- Start threads that listens to other nodes and injects transactions
  sequence_ .
    fmap forkIO .
    M.mapWithKey
      (\remoteNode conn ->
         listenForRemoteTransactions
           (STM.atomically . performTransaction)
           remoteNode
           (connTcpSock conn)) $
    sockets
  -- Listen for circuit transactions from the given node via the given socket.
  return
    ( \gateUpdates
          -- Get current time.
       -> do
        localTime <- Time.getCurrentTime
        transaction <-
          STM.atomically $ do
            acCircuit <- STM.readTVar actuatedCircuitInternalMVar
            -- Get the estimated server time.
            let (estimatedTime, newTimeEstimator) =
                  estimateTime (acTimeEstimator acCircuit) localTime
            -- perform the transaction.
            STM.writeTVar
              actuatedCircuitInternalMVar
              acCircuit {acTimeEstimator = newTimeEstimator}
            let transaction = Transaction estimatedTime gateUpdates
            performTransaction transaction
            return transaction
          -- broadcast the transaction.
        forM_ sockets $ \conn ->
          NetBS.send (connTcpSock conn) (encodeTransaction transaction)
    , mapM_ (Net.close . connTcpSock) sockets)
  where
    (_, ownerNodePort) = hostNamesAndPorts M.! ownerNode
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
      serverAddrInfo <-
        head <$>
        Net.getAddrInfo
          (Just (Net.defaultHints {Net.addrFlags = [Net.AI_PASSIVE]}))
          Nothing
          (Just (show ownerNodePort))
      putStrLn $ "Opening TCP port: " ++ show (Net.addrAddress serverAddrInfo)
      socket <- Net.socket (Net.addrFamily serverAddrInfo) Net.Stream 0
      Net.bind socket (Net.addrAddress serverAddrInfo)
      Net.listen socket 5
      -- Accept connection to designated socket from greater nodes.
      putStrLn "Connecting to remote nodes..."
      let (lesserNodes, greaterNodes) =
            partition (< ownerNode) . filter (/= ownerNode) $
            M.keys hostNamesAndPorts
      let greaterNodesCount = length greaterNodes
      greaterSocketsMapAssocsAsync <-
        async $
        forM [1 .. greaterNodesCount] $ \_
           -- Accept connection.
         -> do
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
              {connTcpSock = remoteSocket, connSockAddr = remoteSocketAddr})
      -- Connect to all lesser nodes
      lesserSocketsMapAssocsAsyncs <-
        forM lesserNodes $ \remoteNode
        -- Connect to remote node.
         ->
          async $ do
            let (remoteHostName, remotPort) = hostNamesAndPorts M.! remoteNode
            remoteAddrInfo <-
              head <$>
              Net.getAddrInfo
                Nothing
                (Just remoteHostName)
                (Just (show remotPort))
            let remoteSockAddr = Net.addrAddress remoteAddrInfo
            putStrLn $ "connecting to: " ++ show remoteSockAddr
            remoteSocket <-
              Net.socket (Net.addrFamily remoteAddrInfo) Net.Stream 0
            -- Connect (with retry)
            let retryWait = 500000
                tryConnect :: IO ()
                tryConnect =
                  catch
                    (Net.connect remoteSocket remoteSockAddr)
                    (\(_ :: IOException) -> do
                       threadDelay retryWait
                       tryConnect)
            tryConnect
            -- Send owner node type.
            _bytesSent <- NetBS.send remoteSocket (encode ownerNode)
            return
              ( remoteNode
              , Connection
                {connTcpSock = remoteSocket, connSockAddr = remoteSockAddr})
      -- Wait for connections to be established.
      greaterSocketsMapAssocs <- wait greaterSocketsMapAssocsAsync
      lesserSocketsMapAssocs <- mapM wait lesserSocketsMapAssocsAsyncs
      let remoteSockets =
            M.fromList (lesserSocketsMapAssocs ++ greaterSocketsMapAssocs)
      putStrLn "Connection established."
      return remoteSockets

-- |Apply the transaction (with possible rollback and replay), updating the internal
-- state and calling listeners.
applyTransaction ::
     forall node. ActuatedCircuit node -> Transaction -> STM.STM ()
applyTransaction (ActuatedCircuit aCircuitMV) transaction@(Transaction time updates) = do
  newCircuit <- applyTransaction' =<< STM.readTVar aCircuitMV
  STM.writeTVar aCircuitMV newCircuit
  where
    applyTransaction' ::
         ActuatedCircuitInternal node -> STM.STM (ActuatedCircuitInternal node)
    applyTransaction' actuatedCircuitInternal = do
      let hist = acHistory actuatedCircuitInternal
          (newerDeltas, oldHistory) = histSplit time hist


      TODO Start from oldHistory (roll back). Then apply the new update .
        Then apply the the newerDeltas (replay)
      let transactions = acHistory actuatedCircuitInternal
      let latestTimeMay =
            case transactions of
              [] -> Nothing
              (Transaction t _, _, _):_ -> Just t
      case fromMaybe GT (compare time <$> latestTimeMay) of
        EQ ->
          error $
          "TODO Cannot currently apply multiple transactions at the same time." ++
          "Need a way to resolve order that is unambiguous accross nodes."
        LT
           -- Rolling back and recreating the circuit state is realtivelly simple,
           -- but how to correctly call the listeners is more a more complicated issue.
           -- In general listeners may have done some IO that needs to be undone,
           -- e.g. started playing a sound file, which should be cancelled with the
           -- current roll back. It should be up to the listener to decide how best
           -- to performe the rollback. For the time being, we assume that no
           -- rollback is required, i.e. listeners will always be called with the
           -- latest value (if cahnged) exactly once per transaction even if a
           -- rollback occured.
         -> do
          error "TODO roll back and replay circuit."
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
          let affectedGates =
                M.keysSet behaviorUpdates `S.union` M.keysSet events
          -- Define the new states by setting the affected states
          return
            ActuatedCircuitInternal
            { acListeners = acListeners actuatedCircuitInternal
            , acHistory =
                ( (transaction, newCircuit, affectedGates) : transactions
                , acInitialState actuatedCircuitInternal)
            , acTimeEstimator = acTimeEstimator actuatedCircuitInternal
            , acDoOnListenersThread =
                acDoOnListenersThread actuatedCircuitInternal
            }
