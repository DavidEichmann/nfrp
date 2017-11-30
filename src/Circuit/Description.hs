{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Module that the user uses to describing the NFRP circuit
module Circuit.Description
  ( Circuit
  , circuitGateKeysByInt
  , applyUpdates
  , CircuitBuilder
  , behaviorValue
  , behaviorDynValueMay
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
  , GateValue
  , GateUpdate(..)
  , gateUpdate
  , GateType(..)
  , GateKey
  , gateKeyToInt
  , GateKey'(..)
  , gateKey'ToInt
  ) where

import Control.Monad.Trans.State.Strict

import Control.Monad (join)
import Data.Dynamic
import Data.Kind (Type)
import Data.List (foldl')
import qualified Data.Map as M
import Data.Serialize (Serialize)
import qualified Data.Set as S
import GHC.Generics

mkCircuit :: State (Circuit node) a -> (a, Circuit node)
mkCircuit circuitBuilder = runState circuitBuilder emptyCircuit

-- | Key to gate in a circuit
newtype GateKey (gateType :: GateType) (a :: Type) = GateKey
  { gateKeyToInt :: Int
  } deriving (Generic, Serialize, Ord, Eq, Show)

class (Typeable a, Serialize a, Eq a) =>
      GateValue a

instance (Typeable a, Serialize a, Eq a) => GateValue a

data GateKey' =
  forall (a :: Type) (gateType :: GateType). (GateValue a) =>
                                             GateKey' (GateKey gateType a)

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
  , circuitGateKeysByInt :: M.Map Int GateKey' -- ^ all gate keys indexed by their internal int value.
  }

data Gate' node =
  forall a. Gate' (Gate node a)

data Gate node a =
  Gate [GateKey'] -- ^ children
       (GateDescription node a)

data GateDescription node a
  = GateLocalE node
  | forall b. (GateValue a, GateValue b) =>
              GateLiftE (b -> a)
                        (E b)
  | (GateValue a) =>
    GateMergeE (a -> a -> a)
               (E a)
               (E a)
  | forall c b. (GateValue a, GateValue b, GateValue c) =>
                GateSample (b -> c -> a)
                           (B b)
                           (E c)
  | (GateValue a) =>
    GateStepper (E a)
  | forall b. (GateValue a, GateValue b) =>
              GateLiftB1 (b -> a)
                         (B b)
  | forall b c. (GateValue a, GateValue b, GateValue c) =>
                GateLiftB2 (b -> c -> a)
                           (B b)
                           (B c)

data GateUpdate =
  forall (gateType :: GateType) a. GateValue a =>
                                   GateUpdate (GateKey gateType a)
                                              a

gateUpdate :: GateValue a => GateKey gt a -> a -> GateUpdate
gateUpdate = GateUpdate

emptyCircuit :: Circuit node
emptyCircuit = Circuit M.empty M.empty M.empty

behaviorValue :: (GateValue a) => B a -> Circuit node -> a
behaviorValue key (Circuit behaviorValues _ _) =
  fromDyn
    (behaviorValues M.! GateKey' key)
    (error "Type mismatch when getting behavior value")

-- | Nothing if an event (or an invalid key)
behaviorDynValueMay :: GateKey' -> Circuit node -> Maybe Dynamic
behaviorDynValueMay key (Circuit behaviorValues _ _) =
  M.lookup key behaviorValues

addChildToParents :: GateKey' -> [GateKey'] -> Circuit node -> Circuit node
addChildToParents child parents (Circuit behaviorValues gates gateKeys) =
  Circuit
    behaviorValues
    (foldl'
       (flip
          (M.adjust
             (\(Gate' (Gate children desc)) ->
                Gate' (Gate (child : children) desc))))
       gates
       parents)
    gateKeys

addBehaviorGate ::
     (GateValue a)
  => a
  -> Gate node a
  -> [GateKey']
  -> CircuitBuilder node (B a)
addBehaviorGate value gate parents = do
  Circuit behaviorValues gates gateKeys <- get
  key <- unsafeNextGateKey
  let key' = GateKey' key
  put
    (Circuit
       (M.insert key' value' behaviorValues)
       (M.insert key' gate' gates)
       (M.insert (gateKeyToInt key) key' gateKeys))
  modify' (addChildToParents key' parents)
  return key
  where
    value' = toDyn value
    gate' = Gate' gate

addEventGate ::
     (GateValue a) => Gate node a -> [GateKey'] -> CircuitBuilder node (E a)
addEventGate gate parents = do
  Circuit behaviorValues gates gateKeys <- get
  key <- unsafeNextGateKey
  let key' = GateKey' key
  put
    (Circuit
       behaviorValues
       (M.insert key' gate' gates)
       (M.insert (gateKeyToInt key) key' gateKeys))
  modify' (addChildToParents (GateKey' key) parents)
  return key
  where
    gate' = Gate' gate

-- Create a gate key. It is unsafe because the resulting key must immediatelly be added before calling again.
unsafeNextGateKey :: CircuitBuilder nodes (GateKey (gateType :: GateType) a)
unsafeNextGateKey = do
  maxGateKey <-
    gets
      (maybe 0 (\(GateKey' (GateKey k), _) -> k) . M.lookupMax . circuitGates)
  return (GateKey (maxGateKey + 1))

-- Exported functions to build the circuit
type CircuitBuilder node a = State (Circuit node) a

type E a = GateKey 'EventGate a

type B a = GateKey 'BehaviorGate a

stepper :: (GateValue a) => a -> E a -> CircuitBuilder node (B a)
stepper initialValue childEvent = do
  assertContainsGate childEvent
  let gate = Gate [] (GateStepper childEvent)
  addBehaviorGate initialValue gate [GateKey' childEvent]

liftB1 ::
     (GateValue a, GateValue b) => (a -> b) -> B a -> CircuitBuilder node (B b)
liftB1 f childBehavior = do
  assertContainsGate childBehavior
  childInitialValue <- gets (behaviorValue childBehavior)
  let gate = Gate [] (GateLiftB1 f childBehavior)
  addBehaviorGate (f childInitialValue) gate [GateKey' childBehavior]

liftB2 ::
     (GateValue a, GateValue b, GateValue c)
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
     (GateValue a, GateValue b) => (a -> b) -> E a -> CircuitBuilder node (E b)
liftE f event = do
  assertContainsGate event
  let gate = Gate [] (GateLiftE f event)
  addEventGate gate [GateKey' event]

mergeE ::
     (GateValue a) => (a -> a -> a) -> E a -> E a -> CircuitBuilder nodes (E a)
mergeE combine eventA eventB = do
  assertContainsGate eventA
  assertContainsGate eventB
  let gate = Gate [] (GateMergeE combine eventA eventB)
  addEventGate gate [GateKey' eventA, GateKey' eventB]

sample ::
     (GateValue a, GateValue b, GateValue c)
  => (a -> b -> c)
  -> B a
  -> E b
  -> CircuitBuilder node (E c)
sample combine behavior event = do
  assertContainsGate behavior
  assertContainsGate event
  let gate = Gate [] (GateSample combine behavior event)
  addEventGate gate [GateKey' behavior, GateKey' event]

-- |Returns the (new circuit, behavior value changes, events).
applyUpdates ::
     Circuit node
  -> [GateUpdate]
  -> (Circuit node, M.Map GateKey' Dynamic, M.Map GateKey' Dynamic)
applyUpdates circuit updates
  -- TODO affected gates may actually a smaller subset due to event filtering (once that is supported)!
 =
  let updatesMap :: M.Map GateKey' Dynamic
      updatesMap =
        M.fromList [(GateKey' key, toDyn val) | GateUpdate key val <- updates]
      possiblyAffectedGates :: S.Set GateKey'
      possiblyAffectedGates =
        foldl'
          accumulateAffectedGates
          S.empty
          [GateKey' key | GateUpdate key _ <- updates]
      events :: M.Map GateKey' (Maybe Dynamic)
      behaviorUpdates :: M.Map GateKey' (Maybe Dynamic)
      (events, behaviorUpdates) = M.mapEither id eventAndBehaviorUpdates
      eventAndBehaviorUpdates ::
           M.Map GateKey' (Either (Maybe Dynamic) (Maybe Dynamic))
      eventAndBehaviorUpdates =
        M.fromList $
        flip map (S.toList possiblyAffectedGates) $ \key' ->
          ( key'
          , case circuitGates circuit M.! key' of
              Gate' (Gate _ desc) ->
                case desc of
                  GateLocalE _ -> Left (M.lookup key' updatesMap)
                  GateLiftE f e ->
                    Left
                      (toDyn . f . fromDyn' <$>
                       join (M.lookup (GateKey' e) events))
                  GateMergeE merge e1 e2 ->
                    Left $ do
                      e1ValueMay <- M.lookup (GateKey' e1) events
                      e2ValueMay <- M.lookup (GateKey' e2) events
                      case (e1ValueMay, e2ValueMay) of
                        (Nothing, Nothing) -> Nothing
                        (Just eValDyn, Nothing) -> Just eValDyn
                        (Nothing, Just eValDyn) -> Just eValDyn
                        (Just e1ValDyn, Just e2ValDyn) ->
                          Just . toDyn $
                          merge (fromDyn' e1ValDyn) (fromDyn' e2ValDyn)
                  GateSample f b e ->
                    Left
                      (do let bVal = fromDyn' (behaviorValues M.! GateKey' b)
                          eventValueMay <- M.lookup (GateKey' e) events
                          toDyn . f bVal . fromDyn' <$> eventValueMay)
                  GateStepper e -> Right (join $ M.lookup (GateKey' e) events)
                  GateLiftB1 f b ->
                    Right . Just . toDyn . f . fromDyn' $
                    behaviorValues M.! GateKey' b
                  GateLiftB2 f b1 b2 ->
                    Right . Just . toDyn $
                    f
                      (fromDyn' $ behaviorValues M.! GateKey' b1)
                      (fromDyn' $ behaviorValues M.! GateKey' b2))
      behaviorValues :: M.Map GateKey' Dynamic
      behaviorValues =
        M.unionWith
          const
          (M.mapMaybe id behaviorUpdates)
          (circuitBehaviorValues circuit)
  in ( Circuit
       { circuitBehaviorValues = behaviorValues
       , circuitGates = circuitGates circuit
       , circuitGateKeysByInt = circuitGateKeysByInt circuit
       }
     , M.mapMaybe id behaviorUpdates
     , M.mapMaybe id events)
  where
    fromDyn' :: Typeable a => Dynamic -> a
    fromDyn' = flip fromDyn (error "Unexpected event type!")
    accumulateAffectedGates :: S.Set GateKey' -> GateKey' -> S.Set GateKey'
    accumulateAffectedGates visited gate
      | S.member gate visited = visited
      | otherwise =
        foldl'
          accumulateAffectedGates
          (S.insert gate visited)
          (childGates circuit gate)

childGates :: Circuit node -> GateKey' -> [GateKey']
childGates circuit key =
  case circuitGates circuit M.! key of
    Gate' (Gate children _) -> children

assertContainsGate ::
     (GateValue a) => GateKey gateType a -> CircuitBuilder nodes ()
assertContainsGate key =
  modify'
    (\circuit@(Circuit _ gates gateKeys) ->
       if M.member (GateKey' key) gates && M.member (gateKeyToInt key) gateKeys
         then circuit
         else error "Key is not part of the circuit.")

instance Show GateKey' where
  show (GateKey' gk) = show gk

gateKey'ToInt :: GateKey' -> Int
gateKey'ToInt (GateKey' gk) = gateKeyToInt gk
