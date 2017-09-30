{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
  ) where

import Control.Concurrent (forkIO)
import Control.Concurrent.Async (async, wait)
import qualified Control.Concurrent.MVar as MV
import Control.Monad (forM, forM_, unless)
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

import Circuit.Description

type Time = Int -- Or long? or timestamp?

data ActuatedCircuitInternal node = ActuatedCircuitInternal
  { acListeners :: M.Map GateKey' [Dynamic]
  -- TODO could separate out the circuit state (M.Map GateKey' Dynamic) from the circuit description (M.Map GateKey' (Gate' node))
  --      then the history would be a single circuit description and many states. Unless the circuitry changes!!!!!! Thats future work
  , acHistory :: [(Transaction, Circuit node)] -- ^ update and result (most recent is at the head)
  , acInitialState :: Circuit node -- ^ initial state.
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
acCurrentState (ActuatedCircuitInternal _ ((_, currentState):_) _) =
  currentState
acCurrentState (ActuatedCircuitInternal _ [] currentState) = currentState

actuate ::
     forall node. (Ord node, Serialize node, Show node)
  => M.Map node Int -- ^ map from node to port number (TODO and IP address)
  -> node -- ^ what node this is.
  -> Circuit node -- ^ The circuit to actuate
  -> [Listener] -- ^ Listeners the will be called whenever the freshest values (includes roll back values!?).
  -> IO (Transaction -> IO (), IO ()) -- ^ (Returns the function to perform local transcations, close sockets)
actuate nodeAddresses ownerNode circuit listeners
  -- See http://www.linuxhowtos.org/C_C++/socket.htm for some networking help.
  -- Open socket
  -- TODO clock synchronization with other nodes
  -- TODO agree on start time? Start actuation on all nodes at the same time.
  -- Create ActuatedCircuit
 = do
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
      }
  let actuatedCircuit = ActuatedCircuit actuatedCircuitInternalMVar
  -- Connect to other nodes.
  sockets <- connect
  -- Create the transaction function.
  let performTransaction = applyTransaction actuatedCircuit
  -- Start threads that listens to other nodes and injects transactions
  sequence_ .
    fmap forkIO . M.mapWithKey (listenForRemoteTransactions performTransaction) $
    sockets
  -- |Listen for circuit transactions from the given node via the given socket.
  return
    ( (\transaction
        -- perform the transaction.
        -> do
          performTransaction transaction
          -- broadcast the transaction.
          forM_ sockets $ \socket ->
            NetBS.send socket (encodeTransaction transaction))
    , mapM_ Net.close sockets
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
            let transaction = decodeTransaction circuit msg
            either
              (\errorMsg -> do
                 putStrLn
                   ("Failed to decode transaction from \"" ++ show node ++ "\":")
                 putStrLn ("Error Message: " ++ errorMsg)
                 putStr "Data: "
                 BS8.putStrLn msg)
              performTransaction
              transaction
            loop
    -- |Connect to all other nodes. Returns a map from nodes (excluding ownerNode)
    -- to a Socket used to comunicate with the node.
    connect :: IO (M.Map node Net.Socket)
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
        -- Accept connection.
         -> do
          (remoteSocket, _remoteSocketAddr) <- Net.accept socket
        -- Read remote node type
          (remoteNode :: node) <-
            either
              (\str ->
                 error ("Failed to parse node type from remote node: " ++ str))
              id .
            decode <$>
            NetBS.recv remoteSocket recvBufferSize :: IO node
          return (remoteNode, remoteSocket)
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
            remoteSocket <- Net.socket Net.AF_INET Net.Stream 0
            Net.connect remoteSocket remoteSockAddr
            -- Send owner node type.
            _bytesSent <- NetBS.send remoteSocket (encode ownerNode)
            return (remoteNode, remoteSocket)
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
            }