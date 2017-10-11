{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Module that the user uses to describing the NFRP circuit
module Circuit.Description
  -- ( Circuit
  -- , circuitGateKeysByInt
  -- , applyUpdates
  -- , CircuitBuilder
  -- , behaviorValue
  -- , mkCircuit
  -- , E
  -- , localE
  -- , liftE
  -- , mergeE
  -- , sample
  -- , B
  -- , stepper
  -- , liftB1
  -- , liftB2
  -- , GateValue
  -- , GateUpdate(..)
  -- , gateUpdate
  -- , GateType(..)
  ( Availability(..)
  , GateType(..)
  , GateKey
  --, gateKeyToInt
  --, GateKey'(..)
  --, gateKey'ToInt
  ) where

import Data.Kind (Type)
import Data.Serialize (Serialize)
import GHC.Generics

data GateType
  = BehaviorGate
  | EventGate

data Availability node
  = Shared
  | Owned node

-- | Key to gate in a circuit
newtype GateKey
  (node :: Type)
  (gateType :: GateType)
  (availability :: Availability node)
  -- TODO (nodeTrace :: [node])
  (a :: Type)
    = GateKey
      { gateKeyToInt :: Int
      } deriving (Generic, Serialize, Ord, Eq, Show)



data Node = NodeA | NodeB

x :: GateKey
      Node
      'BehaviorGate
      ('Owned 'NodeA)
      Int
x = undefined

{-
data Gate node (av :: Availability node) a =
  Gate  [GateKey'] -- ^ children
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
  | forall b c. (GateValue a, GateValue b, GateValue c) =>
                GateSample (b -> c -> a)
                           (B b)
                           (E c)
  | (GateValue a) =>
    GateStepper (E a)
  | forall b. (GateValue a, GateValue b) =>
              GateLiftB1 (b -> a)
                         (B b)
  | forall c b. (GateValue a, GateValue b, GateValue c) =>
                GateLiftB2 (b -> c -> a)
                           (B b)
                           (B c)
-}
