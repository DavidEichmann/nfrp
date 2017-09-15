{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module SumExample where

import Control.Monad
import Data.IORef
import Data.Kind
import Data.Proxy

import Circuit.Description

data Node
  = Server
  | Client

type instance Inputs Node Server = ServerInputs

newtype ServerInputs = ServerInputs
  { serverIntAddHandler :: AddHandler Int
  }

type instance Inputs Node Client = ClientInputs

newtype ClientInputs = ClientInputs
  { clientIntAddHandler :: AddHandler Int
  }

data SumOuts = SumOuts
  { serverInt :: GateKey BehaviorGate Int
  , clientInt :: GateKey BehaviorGate Int
  , sum :: GateKey BehaviorGate Int
  }

sumOuts :: SumOuts
sumCircuit :: Circuit Node
(sumOuts, sumCircuit) = mkCircuit $ do
  -- Setup network
 =
  serverIntB <- stepper 0 =<< localE (Proxy @Server) serverIntAddHandler
  clientIntB <- stepper 0 =<< localE (Proxy @Client) clientIntAddHandler
  sumB <- liftB2 (+) serverIntB clientIntB
  -- return observations
  return SumOuts
  { serverInt = serverB
  , clientInt = clientB
  , sum = sumB
  }
