{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Module that the user uses to describing the NFRP circuit
module Circuit.Description
  ( Inputs
  , Handler
  , AddHandler
  , Event
  , RefEvent
  , localE
  , liftE
  , mergeE
  , sample
  , Behavior
  , RefBehavior
  , stepper
  , liftB1
  , liftB2
  , liftB3
  ) where

import Control.Monad
import Data.IORef
import Data.Kind
import Data.Proxy

type Handler a = a -> IO ()

type AddHandler a = Handler a -> IO ()

data RemoteValue =
  RemoteValue

type RefEvent node a = IORef (Event node a)

type RefBehavior node a = IORef (Behavior node a)

type family Inputs node (self :: node)

data Event node a
  = forall (owner :: node). LocalE (Proxy owner)
                                   (Inputs node owner -> AddHandler a)
  | forall b. LiftE (b -> a)
                    (RefEvent node b)
  | MergeE (a -> a -> a)
           (RefEvent node a)
           (RefEvent node a)
  | forall b c. Sample (b -> c -> a)
                       (RefBehavior node b)
                       (RefEvent node c)

localE ::
     Proxy owner -> (Inputs node owner -> AddHandler a) -> IO (RefEvent node a)
localE ownerProxy getAddHandler = newIORef (LocalE ownerProxy getAddHandler)

liftE :: (b -> a) -> RefEvent node b -> IO (RefEvent node a)
liftE f e = newIORef $ LiftE f e

mergeE ::
     (a -> a -> a) -> RefEvent node a -> RefEvent node a -> IO (RefEvent node a)
mergeE combine e1 e2 = newIORef $ MergeE combine e1 e2

sample ::
     (b -> c -> a)
  -> RefBehavior node b
  -> RefEvent node c
  -> IO (RefEvent node a)
sample f b e = newIORef $ Sample f b e

-- Behavior inputAddHandlerCollection behavoirCollection ValueType
-- This is a description of a networked behavior
data Behavior node a
  = Stepper a
            (RefEvent node a)
  | forall b. LiftB1 (b -> a)
                     (RefBehavior node b)
  | forall c b. LiftB2 (b -> c -> a)
                       (RefBehavior node b)
                       (RefBehavior node c)

stepper :: a -> RefEvent node a -> IO (RefBehavior node a)
stepper initiaValue e = newIORef $ Stepper initiaValue e

liftB1 :: (a -> b) -> RefBehavior node a -> IO (RefBehavior node b)
liftB1 f ba = newIORef $ LiftB1 f ba

liftB2 ::
     (a -> b -> c)
  -> RefBehavior node a
  -> RefBehavior node b
  -> IO (RefBehavior node c)
liftB2 f ba bb = newIORef $ LiftB2 f ba bb

liftB3 ::
     (a -> b -> c -> d)
  -> RefBehavior node a
  -> RefBehavior node b
  -> RefBehavior node c
  -> IO (RefBehavior node d)
liftB3 f ba bb bc = do
  fab <- liftB2 f ba bb
  liftB2 ($) fab bc
