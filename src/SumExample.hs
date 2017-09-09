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
  { serverInt :: Int
  , clientInt :: Int
  , sum :: Int
  }

mkSumBeh :: IO (RefBehavior Node SumOuts)
mkSumBeh
  -- Setup network
 = do
  serverIntB <- stepper 0 =<< localE (Proxy @Server) serverIntAddHandler
  clientIntB <- stepper 0 =<< localE (Proxy @Client) clientIntAddHandler
  sumB <- liftB2 (+) serverIntB clientIntB
  -- return observations
  liftB3 SumOuts serverIntB clientIntB sumB
