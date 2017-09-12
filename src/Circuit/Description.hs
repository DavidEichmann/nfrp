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
  , Event(..)
  , RefEvent(..)
  , localE
  , liftE
  , mergeE
  , sample
  , Behavior(..)
  , RefBehavior(..)
  , stepper
  , liftB1
  , liftB2
  , liftB3
  ) where

import Control.Monad
import Data.Dynamic
import Data.Kind
import Data.Proxy
import Data.Unique

type Handler a = a -> IO ()

type AddHandler a = Handler a -> IO ()

data RemoteValue =
  RemoteValue

data RefEvent node a =
  RefEvent Unique
           (Event node a)

data RefBehavior node a =
  RefBehavior Unique
              (Behavior node a)

type family Inputs node (self :: node)

data Event node a
  = forall (owner :: node). LocalE (Proxy owner)
                                   (Inputs node owner -> AddHandler a)
  | forall b. Typeable b =>
              LiftE (b -> a)
                    (RefEvent node b)
  | MergeE (a -> a -> a)
           (RefEvent node a)
           (RefEvent node a)
  | forall c b. (Typeable b, Typeable c) =>
                Sample (b -> c -> a)
                       (RefBehavior node b)
                       (RefEvent node c)

-- Behavior inputAddHandlerCollection behavoirCollection ValueType
-- This is a description of a networked behavior
data Behavior node a
  = Stepper a
            (RefEvent node a)
  | forall b. Typeable b =>
              LiftB1 (b -> a)
                     (RefBehavior node b)
  | forall b c. (Typeable b, Typeable c) =>
                LiftB2 (b -> c -> a)
                       (RefBehavior node b)
                       (RefBehavior node c)

newRefEvent :: Event node a -> IO (RefEvent node a)
newRefEvent event = do
  key <- newUnique
  return (RefEvent key event)

newRefBehavior :: Behavior node a -> IO (RefBehavior node a)
newRefBehavior behavior = do
  key <- newUnique
  return (RefBehavior key behavior)

localE ::
     Proxy owner -> (Inputs node owner -> AddHandler a) -> IO (RefEvent node a)
localE ownerProxy getAddHandler = newRefEvent (LocalE ownerProxy getAddHandler)

liftE :: Typeable b => (b -> a) -> RefEvent node b -> IO (RefEvent node a)
liftE f e = newRefEvent $ LiftE f e

mergeE ::
     (a -> a -> a) -> RefEvent node a -> RefEvent node a -> IO (RefEvent node a)
mergeE combine e1 e2 = newRefEvent $ MergeE combine e1 e2

sample ::
     (Typeable b, Typeable c)
  => (b -> c -> a)
  -> RefBehavior node b
  -> RefEvent node c
  -> IO (RefEvent node a)
sample f b e = newRefEvent $ Sample f b e

stepper :: a -> RefEvent node a -> IO (RefBehavior node a)
stepper initiaValue e = newRefBehavior $ Stepper initiaValue e

liftB1 ::
     (Typeable a, Typeable b)
  => (a -> b)
  -> RefBehavior node a
  -> IO (RefBehavior node b)
liftB1 f ba = newRefBehavior $ LiftB1 f ba

liftB2 ::
     (Typeable a, Typeable b, Typeable c)
  => (a -> b -> c)
  -> RefBehavior node a
  -> RefBehavior node b
  -> IO (RefBehavior node c)
liftB2 f ba bb = newRefBehavior $ LiftB2 f ba bb

liftB3 ::
     (Typeable a, Typeable b, Typeable c, Typeable d)
  => (a -> b -> c -> d)
  -> RefBehavior node a
  -> RefBehavior node b
  -> RefBehavior node c
  -> IO (RefBehavior node d)
liftB3 f ba bb bc = do
  fab <- liftB2 f ba bb
  liftB2 ($) fab bc
