{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Module that the user uses to describing the NFRP circuit
module Circuit.Description
  ( Circuit
  , CircuitBuilder
  , behaviorValue
  , mkCircuit
  , E
  , localE
  , liftE
  , mergeE
  , sample
  , B
  , stepper
  , liftB1
  , liftB2
  , GateType(..)
  , GateKey
  , GateKey'(..)
  ) where

import Control.Monad.Trans.State.Strict

import Data.Dynamic
import Data.List (foldl')
import qualified Data.Map as M

mkCircuit :: State (Circuit node) a -> (a, Circuit node)
mkCircuit circuitBuilder = runState circuitBuilder emptyCircuit

-- | Key to gate in a circuit
newtype GateKey (gateType :: GateType) a =
  GateKey Int
  deriving (Ord, Eq)

data GateKey' =
  forall (gateType :: GateType) a. GateKey' (GateKey gateType a)

instance Eq GateKey' where
  GateKey' (GateKey a) == GateKey' (GateKey b) = a == b

instance Ord GateKey' where
  compare (GateKey' (GateKey a)) (GateKey' (GateKey b)) = compare a b

data GateType
  = BehaviorGate
  | EventGate

data Circuit node = Circuit
  -- TODO use "forall a. GateKey *BehaviorGate* a" for behavior values
  { circuitBehaviorValues :: M.Map GateKey' Dynamic -- ^ value of all the behavior gates
  , circuitGates :: M.Map GateKey' (Gate' node) -- ^ description of all gates
  }

data Gate' node =
  forall a. Gate' (Gate node a)

data Gate node a =
  Gate [GateKey'] -- ^ children
       (GateDescription node a)

data GateDescription node a
  = GateLocalE node
  | forall b. Typeable b =>
              GateLiftE (b -> a)
                        (B b)
  | GateMergeE (a -> a -> a)
               (E a)
               (E a)
  | forall b c. (Typeable b, Typeable c) =>
                GateSample (b -> c -> a)
                           (B b)
                           (E c)
  | GateStepper (E a)
  | forall b. Typeable b =>
              GateLiftB1 (b -> a)
                         (B b)
  | forall c b. (Typeable b, Typeable c) =>
                GateLiftB2 (b -> c -> a)
                           (B b)
                           (B c)

emptyCircuit :: Circuit node
emptyCircuit = Circuit M.empty M.empty

behaviorValue :: Typeable a => B a -> Circuit node -> a
behaviorValue key (Circuit behaviorValues _) =
  fromDyn
    (behaviorValues M.! GateKey' key)
    (error "Type mismatch when getting behavior value")

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
     Typeable a => a -> Gate node a -> [GateKey'] -> CircuitBuilder node (B a)
addBehaviorGate value gate parents = do
  Circuit behaviorValues gates <- get
  key <- unsafeNextGateKey
  let key' = GateKey' key
  put
    (Circuit (M.insert key' value' behaviorValues) (M.insert key' gate' gates))
  modify' (addChildToParents key' parents)
  return key
  where
    value' = toDyn value
    gate' = Gate' gate

addEventGate ::
     Typeable a => Gate node a -> [GateKey'] -> CircuitBuilder node (E a)
addEventGate gate parents = do
  Circuit behaviorValues gates <- get
  key <- unsafeNextGateKey
  let key' = GateKey' key
  put (Circuit behaviorValues (M.insert key' gate' gates))
  modify' (addChildToParents (GateKey' key) parents)
  return key
  where
    gate' = Gate' gate

-- Create a gate key. It is unsafe because the resulting key must immediatelly be added before calling again.
unsafeNextGateKey :: CircuitBuilder nodes (GateKey (gateType :: GateType) a)
unsafeNextGateKey = do
  GateKey' (GateKey maxGateKey) <- gets (fst . M.findMax . circuitGates)
  return (GateKey (maxGateKey + 1))

-- Exported functions to build the circuit
type CircuitBuilder node a = State (Circuit node) a

type E a = GateKey 'EventGate a

type B a = GateKey 'BehaviorGate a

stepper :: Typeable a => a -> E a -> CircuitBuilder node (B a)
stepper initialValue childEvent = do
  assertContainsGate childEvent
  let gate = Gate [] (GateStepper childEvent)
  addBehaviorGate initialValue gate [GateKey' childEvent]

liftB1 ::
     (Typeable a, Typeable b) => (a -> b) -> B a -> CircuitBuilder node (B b)
liftB1 f childBehavior = do
  assertContainsGate childBehavior
  childInitialValue <- gets (behaviorValue childBehavior)
  let gate = Gate [] (GateLiftB1 f childBehavior)
  addBehaviorGate (f childInitialValue) gate [GateKey' childBehavior]

liftB2 ::
     (Typeable a, Typeable b, Typeable c)
  => (a -> b -> c)
  -> B a
  -> B b
  -> CircuitBuilder node (B c)
liftB2 f behaviorA behaviorB = do
  assertContainsGate behaviorA
  assertContainsGate behaviorB
  childAInitialValue <- gets (behaviorValue behaviorA)
  childBInitialValue <- gets (behaviorValue behaviorB)
  let gate = Gate [] (GateLiftB2 f behaviorA behaviorB)
  addBehaviorGate
    (f childAInitialValue childBInitialValue)
    gate
    [GateKey' behaviorA, GateKey' behaviorB]

-- The type is infered, but when inserted doesnt work!!!!
-- localE :: Typeable a => node -> CircuitBuilder node (E a)
localE ownder = do
  let gate = Gate [] (GateLocalE ownder)
  addEventGate gate []

liftE ::
     (Typeable a, Typeable b) => (a -> b) -> B a -> CircuitBuilder node (E b)
liftE f event = do
  assertContainsGate event
  let gate = Gate [] (GateLiftE f event)
  addEventGate gate [GateKey' event]

mergeE ::
     Typeable a => (a -> a -> a) -> E a -> E a -> CircuitBuilder nodes (E a)
mergeE combine eventA eventB = do
  assertContainsGate eventA
  assertContainsGate eventB
  let gate = Gate [] (GateMergeE combine eventA eventB)
  addEventGate gate [GateKey' eventA, GateKey' eventB]

sample ::
     (Typeable a, Typeable b, Typeable c)
  => (a -> b -> c)
  -> B a
  -> E b
  -> CircuitBuilder node (E c)
sample combine behavior event = do
  assertContainsGate behavior
  assertContainsGate event
  let gate = Gate [] (GateSample combine behavior event)
  addEventGate gate [GateKey' behavior, GateKey' event]

{-
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
        return (addBehaviorGate gateKey initialValue gate [GateKey' childKey])
      -- TODO
      (LiftB1 f childB) -> do
        childKey <- buildCircuitB' childB
        childInitialValue <- gets (behaviorValue childKey)
        let gate = Gate [] (GateLiftB1 f childKey)
        return
          (addBehaviorGate
             gateKey
             (f childInitialValue)
             gate
             [GateKey' childKey])
      (LiftB2 f childAB childBB) -> do
        childAKey <- buildCircuitB' childAB
        childBKey <- buildCircuitB' childBB
        childAInitialValue <- gets (behaviorValue childAKey)
        childBInitialValue <- gets (behaviorValue childBKey)
        let gate = Gate [] (GateLiftB2 f childAKey childBKey)
        return
          (addBehaviorGate
             gateKey
             (f childAInitialValue childBInitialValue)
             gate
             [GateKey' childAKey, GateKey' childBKey])
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
    case event of
      (LocalE ownerProxy) -> error "TODO"
      (LiftE x1 x2) -> undefined
      (MergeE x1 x2 x3) -> undefined
      (Sample x1 x2 x3) -> undefined
  return gateKey
-}
assertContainsGate :: GateKey gateType a -> CircuitBuilder nodes ()
assertContainsGate key =
  modify'
    (\circuit@(Circuit _ gates) ->
       if M.member (GateKey' key) gates
         then circuit
         else error "Key is not part of the circuit.")
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
