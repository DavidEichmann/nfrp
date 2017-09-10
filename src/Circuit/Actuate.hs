{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Module to actuate a circuit description
module Circuit.Actuate
  ( actuate
  ) where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.State.Strict

import Data.Dynamic
import Data.IORef
import Data.Kind
import Data.List (foldl')
import qualified Data.Map as M
import Data.Proxy
import Data.Unique

import Circuit.Description

-- TODO Use a more type safe system rather than Data.Dynamic.
-- Actuate a circuit, listening to input and calling the output handler.
actuate ::
     M.Map node Int -- ^ map from node to port number (TODO and IP address)
  -> Proxy (owner :: node)
  -> Inputs node owner
  -> RefBehavior node output
  -> IO (Handler output)
actuate nodeAddresses ownerProxy inputs circuitDescription
  -- TODO clock synchronization with other nodes
  -- TODO agree on start time? Start actuation on all nodes at the same time.
 = do
  error "TODO Compile the circuit?"
  error "TODO return the AddHandler for the circuit."

type Time = Int -- Or long? or timestamp?

-- | Key to gate in a circuit
newtype GateKey (gateType :: GateType) a = GateKey
  { gateKey' :: Unique
  }

type GateKey' = Unique

data GateType
  = BehaviorGate
  | EventGate

data Circuit node =
  Circuit (M.Map GateKey' Dynamic) -- ^ value of all the behavior gates
          (M.Map GateKey' (Gate' node)) -- ^ description of all gates

data Gate' node =
  forall a. Gate' (Gate node a)

data Gate node a =
  Gate [GateKey'] -- ^ children
       (GateDescription node a)

-- TODO separate Behaviors/events?
data GateDescription node a
  = forall (owner :: node). GateLocalE (Proxy owner)
                                       (Inputs node owner -> AddHandler a)
  | forall b. Typeable b =>
              GateLiftE (b -> a)
                        (GateKey BehaviorGate b)
  | GateMergeE (a -> a -> a)
               (GateKey EventGate a)
               (GateKey EventGate a)
  | forall c b. (Typeable b, Typeable c) =>
                GateSample (b -> c -> a)
                           (GateKey BehaviorGate b)
                           (GateKey EventGate c)
  | GateStepper (GateKey EventGate a)
  | forall b. Typeable b =>
              GateLiftB1 (b -> a)
                         (GateKey BehaviorGate b)
  | forall b c. (Typeable b, Typeable c) =>
                GateLiftB2 (b -> c -> a)
                           (GateKey BehaviorGate b)
                           (GateKey BehaviorGate c)

data Transaction =
  Transaction Time
              (M.Map GateKey' Dynamic)

-- TODO could separate out the circuit state (M.Map GateKey' Dynamic) from the circuit description (M.Map GateKey' (Gate' node))
--      then the history would be a single circuit description and many states. Unless the circuitry changes!!!!!! Thats future work
data CircuitHistory node a =
  CircuitHistory [(Transaction, Circuit node)] -- ^ update and result (most recent is at the front)
                 (Circuit node) -- ^ initial state.

emptyCircuit :: Circuit node
emptyCircuit = Circuit M.empty M.empty

addChildToParents :: GateKey' -> [GateKey'] -> Circuit node -> Circuit node
addChildToParents child parents (Circuit behaviorValues gates) =
  Circuit
    behaviorValues
    (foldl'
       (flip
          (M.adjust
             (\(Gate' (Gate children desc)) ->
                Gate' (Gate (child : children) desc))))
       gates
       parents)

addBehaviorGate ::
     Typeable a
  => GateKey BehaviorGate a
  -> a
  -> Gate node a
  -> [GateKey']
  -> Circuit node
  -> Circuit node
addBehaviorGate key value gate parents (Circuit behaviorValues gates) =
  addChildToParents
    (gateKey' key)
    parents
    (Circuit (M.insert key' value' behaviorValues) (M.insert key' gate' gates))
  where
    key' = gateKey' key
    value' = toDyn value
    gate' = Gate' gate

addEventGate ::
     Typeable a
  => GateKey EventGate a
  -> Gate node a
  -> [GateKey']
  -> Circuit node
  -> Circuit node
addEventGate key gate parents (Circuit behaviorValues gates) =
  addChildToParents
    (gateKey' key)
    parents
    (Circuit behaviorValues (M.insert key' gate' gates))
  where
    key' = gateKey' key
    gate' = Gate' gate

buildCircuitB ::
     forall node a. Typeable a
  => RefBehavior node a
  -> (GateKey BehaviorGate a, Circuit node)
buildCircuitB b = runState (buildCircuitB' b) emptyCircuit

buildCircuitB' ::
     forall node a. Typeable a
  => RefBehavior node a
  -> State (Circuit node) (GateKey BehaviorGate a)
buildCircuitB' (RefBehavior key behavior)
  -- Check if the gate already exists
 = do
  gateAlreadyCreated <- gets (\(Circuit _ gates) -> M.member key gates)
  let gateKey = GateKey key
  unless gateAlreadyCreated $
    modify =<<
    case behavior of
      (Stepper initialValue childE) -> do
        childKey <- buildCircuitE' childE
        let gate = Gate [] (GateStepper childKey)
        return (addBehaviorGate gateKey initialValue gate [gateKey' childKey])
      --
      --
      --
      -- TODO
      (LiftB1 pattern1 pattern2) -> undefined
      (LiftB2 pattern1 pattern2 pattern3) -> undefined
  return gateKey

buildCircuitE' ::
     forall node a. Typeable a
  => RefEvent node a
  -> State (Circuit node) (GateKey EventGate a)
buildCircuitE' (RefEvent key event) = do
  gateAlreadyCreated <- gets (\(Circuit _ gates) -> M.member key gates)
  let gateKey = GateKey key
  unless gateAlreadyCreated $
    modify =<<
    case event
      --
      --
      --
      -- TODO
          of
      x -> undefined
  return gateKey
{-
type Handler a = a -> IO ()

type AddHandler a = Handler a -> IO ()

-- c -> current node
-- o -> owner node
-- a -> value type
type family LocalInput (node :: nodes) (owner :: nodes) a where
  LocalInput owner owner a = AddHandler a
  LocalInput _ owner a = ()

data PNEvent (ins :: nodes -> *) (outs :: nodes -> *) a
  = forall (owner :: nodes) (node :: nodes). LocalE (Proxy owner)
                                                   (ins node -> AddHandler a)
  | forall b. LiftE (b -> a) (PNEvent ins outs b)
  | MergeE (a -> a -> a) (PNBehavior ins outs a) (PNBehavior ins outs a)

-- PNBehavior inputAddHandlerCollection behavoirCollection ValueType
-- This is a description of a networked behavior
data PNBehavior (ins :: nodes -> *) (outs :: nodes -> *) a
  = forall b. LiftB1 (b -> a)
                    (NBehavior ins outs b)
  | forall b c. LiftB2 (b -> c -> a)
                      (NBehavior ins outs b)
                      (NBehavior ins outs c)

newtype NBehavior (ins :: nodes -> *) (outs :: nodes -> *) a =
  NBehavior (IORef (PNBehavior ins outs a))

nBeh :: PNBehavior ins outs a -> IO (NBehavior ins outs a)
nBeh pnbeh = NBehavior <$> newIORef pnbeh

lift1 :: (a -> b) -> NBehavior ins outs a -> IO (NBehavior ins outs b)
lift1 f ba = nBeh $ LiftB1 f ba

lift2 ::
     (a -> b -> c)
  -> NBehavior ins outs a
  -> NBehavior ins outs b
  -> IO (NBehavior ins outs c)
lift2 f ba bb = nBeh $ LiftB2 f ba bb

data Behavior' =
  forall a. Behavior' (Behavior a)

newtype Behavior a =
  Behavior (Node a)

newtype BehaviorSink a =
  BehaviorSink (Node a)

data BehaviorSinkUpdate a =
  BehaviorSinkUpdate (BehaviorSink a)
                     a

data BehaviorSinkUpdate' =
  forall a. BehaviorSinkUpdate' (BehaviorSinkUpdate a)

data Node a =
  Node (IORef a) -- ^ value.
       (IORef Bool) -- ^ is valid.
       (IO a) -- ^ calculate the value.
       [Behavior'] -- ^ parent behaviors.
       [Behavior'] -- ^ child behaviors.
       (IORef [a -> IO ()]) -- ^ listeners.

data Node' =
  forall a. Node' (Node a)

addHandler :: Node a -> Handler a -> IO ()
addHandler (Node _ _ _ _ _ lsR) handler = modifyIORef' lsR (handler :)

fromLocalInput ::
     forall (node :: nodes) (owner :: nodes) a (ins :: nodes -> *) (outs :: nodes -> *).
     (ins node -> AddHandler a)
  -> IO (NBehavior ins outs a)
fromLocalInput addH = nBeh (Local (Proxy @owner) addH)

getBeh :: Node a -> IO a
getBeh (Node valueR isValidR calc _ _ _) = do
  isValid <- readIORef isValidR
  if isValid
    then readIORef valueR
    else do
      newValue <- calc
      writeIORef valueR newValue
      writeIORef isValidR True
      return newValue

-- Invalidate the node and its children.
-- returns newly invalidated nodes that have listeners
invalidate :: Node' -> IO [Node']
invalidate node@(Node' (Node _ isValidR _ _ cs lsR)) = do
  isValid <- readIORef isValidR
  if not isValid
    then return []
    else do
      writeIORef isValidR False
      ls <- readIORef lsR
      childInvalidations <-
        concat <$>
        mapM (invalidate . (\(Behavior' (Behavior node)) -> Node' node)) cs
      return $
        if null ls
          then childInvalidations
          else node : childInvalidations

transaction :: [BehaviorSinkUpdate'] -> IO ()
transaction updates
  -- Invalidate recursivelly with early termination. Keep track of nodes with listeners.
 = do
  observedNodes <-
    concat <$>
    forM
      updates
      (\(BehaviorSinkUpdate' (BehaviorSinkUpdate behaviorSink newValue)) ->
         setBeh behaviorSink newValue)
  -- Update nodes with listeners and fire all listeners.
  -- TODO without events an explicite update is not needed
  forM_ observedNodes $ \(Node' node@(Node _ _ _ _ _ lsR)) -> do
    ls <- readIORef lsR
    val <- getBeh node
    forM_ ls (\l -> l val)

-- Returns newly invalidated nodes.
setBeh :: BehaviorSink a -> a -> IO [Node']
setBeh (BehaviorSink node) newValue = do
  let (Node valueR _ _ _ _ _) = node
  observedNodesCurrent <- invalidate (Node' node)
  writeIORef valueR newValue
  return observedNodesCurrent
-}
