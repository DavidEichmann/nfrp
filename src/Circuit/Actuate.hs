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

import Data.Dynamic
import Data.IORef
import qualified Data.Map as M

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
  forall a (gateType :: GateType). GateUpdate (GateKey gateType a)
                                              a

data Transaction =
  Transaction Time
              [GateUpdate]

-- import Circuit.Description
-- TODO Use a more type safe system rather than Data.Dynamic.
-- Actuate a circuit, listening to input and calling the output handler.
actuate ::
     M.Map node Int -- ^ map from node to port number (TODO and IP address)
  -> node -- ^ what node this is.
  -> Circuit node -- ^ The circuit to actuate
  -> IO (ActuatedCircuit node) -- ^ Returns the actuated circuit.
actuate _nodeAddresses _ownerNode _circuit
  -- TODO clock synchronization with other nodes
  -- TODO agree on start time? Start actuation on all nodes at the same time.
 = error "TODO return the AddHandler for the circuit."

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
