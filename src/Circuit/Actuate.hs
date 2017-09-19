{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Module to actuate a circuit description
module Circuit.Actuate
  ( ActuatedCircuit
  , actuate
  , subscribeB
  , applyTransaction
  ) where

import Control.Concurrent.Async (async, wait)
import Control.Exception (throwIO)
import Control.Monad (forM, when)
import qualified Data.ByteString as BS
import Data.Dynamic
import Data.Either (either)
import Data.IORef
import Data.List (partition)
import qualified Data.Map as M
import Data.Serialize (Serialize, decode, encode)
import qualified Network.Socket as Net
import qualified Network.Socket.ByteString as NetBS

import Circuit.Description

type Time = Int -- Or long? or timestamp?

data ActuatedCircuit node = ActuactedCircuit
  { listeners :: IORef (M.Map GateKey' [Dynamic])
  , circuitHitory :: IORef (CircuitHistory node)
  }

-- TODO could separate out the circuit state (M.Map GateKey' Dynamic) from the circuit description (M.Map GateKey' (Gate' node))
--      then the history would be a single circuit description and many states. Unless the circuitry changes!!!!!! Thats future work
data CircuitHistory node =
  CircuitHistory [(Transaction, Circuit node)] -- ^ update and result (most recent is at the front)
                 (Circuit node) -- ^ initial state.

data GateUpdate =
  forall (gateType :: GateType) a. GateUpdate (GateKey gateType a)
                                              a

data Transaction =
  Transaction Time
              [GateUpdate]

-- TODO is there a more optimal way to get a safe buffer size?
--      Could make this much smaller then read further if necessary, but this
--      makes parsing more complicated :-(
recvBufferSize :: Int
recvBufferSize = 4096

currentCircuitState :: ActuatedCircuit node -> IO (Circuit node)
currentCircuitState aCircuit = do
  CircuitHistory transactions initialState <- readIORef (circuitHitory aCircuit)
  return $
    case transactions of
      [] -> initialState
      (_, state):_ -> state

-- subscribeB :: ActuatedCircuit node -> B a -> (a -> IO ()) -> IO ()
subscribeB :: Typeable a => ActuatedCircuit node -> B a -> (a -> IO ()) -> IO ()
subscribeB aCircuit behavior listener
 -- Initial call to listener.
 = do
  circuitState <- currentCircuitState aCircuit
  listener (behaviorValue behavior circuitState)
 -- Add listener for further changes.
  modifyIORef
    (listeners aCircuit)
    (M.alter
       (\case
          Just ls -> Just (listener' : ls)
          Nothing -> Just [listener'])
       (GateKey' behavior))
  where
    listener' = toDyn listener

-- import Circuit.Description
-- TODO Use a more type safe system rather than Data.Dynamic.
-- Actuate a circuit, listening to input and calling the output handler.
-- Protocol:
--  - Open designated socket
--  - in parallel:
--    - Connect to all lesser nodes
--      - On connecting, send ownerNode to identify self.
--    - accept connection to designated socket from greater nodes
--  - All nodes are connected to all other nodes now.
--  - ???
actuate ::
     forall node. (Ord node, Serialize node, Show node)
  => M.Map node Int -- ^ map from node to port number (TODO and IP address)
  -> node -- ^ what node this is.
  -> Circuit node -- ^ The circuit to actuate
  -> IO (ActuatedCircuit node) -- ^ Returns the actuated circuit.
actuate nodeAddresses ownerNode _circuit
  -- See http://www.linuxhowtos.org/C_C++/socket.htm for some networking help.
  -- Open socket
 = do
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
        partition (< ownerNode) . filter (/= ownerNode) $ M.keys nodeAddresses
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
          (\str -> error ("Failed to parse node type from remote node: " ++ str))
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
  -- TODO clock synchronization with other nodes
  -- TODO agree on start time? Start actuation on all nodes at the same time.
  return $ error "TODO use the network connection to actuate the circuit"

-- TODO make this thread safe!! Many applyTransactions happening at about the same time.
applyTransaction :: ActuatedCircuit node -> Transaction -> IO ()
applyTransaction aCircuit (Transaction time updates) = do
  CircuitHistory oldTransactions _ <- readIORef (circuitHitory aCircuit)
  let latestTime =
        case oldTransactions of
          [] -> minBound
          (Transaction t _, _):_ -> t
  case time `compare` latestTime of
    LT -> error "TODO roll back and replay aircuit."
    EQ ->
      error $
      "TODO Cannot currently apply multiple transactions at the same time." ++
      "Need a way to resolve order that is unambiguous accross nodes."
    GT ->
      error "TODO all the crazy code to update the circuit and fire listeners."
