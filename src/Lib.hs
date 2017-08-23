{-# LANGUAGE ExistentialQuantification #-}

module Lib where

import Control.Monad
import Data.IORef

data Behavior a
  = Sink (BehaviorSink a)
  | forall b. Lift1 (b -> a)
                    (Behavior b)
  | forall b c. Lift2 (b -> c -> a)
                      (Behavior b)
                      (Behavior c)

data BehaviorValue a
  = BehaviorValue a
  | forall b. BehaviorValue1 a
                             (BehaviorValue b)
  | forall b c. BehaviorValue2 a
                               (BehaviorValue b)

data BehaviorSink a =
  BehaviorSink (IORef a) -- ^Value
               (IORef [a -> IO ()]) -- ^Listeners

bvValue :: BehaviorValue a -> a
bvValue (BehaviorValue x) = x
bvValue (BehaviorValue1 x _) = x
bvValue (BehaviorValue2 x _) = x

evaluateFull :: Behavior a -> IO (BehaviorValue a)
evaluateFull (Sink (BehaviorSink v _)) = BehaviorValue <$> readIORef v
evaluateFull (Lift1 f b) = do
  e <- evaluateFull b
  return (BehaviorValue1 (f (bvValue e)) e)

-- evaluateFull (Lift2 f b c) = BehaviorValue2 . f <$> evaluate b <*> evaluate c
evaluate :: Behavior a -> IO a
evaluate b = bvValue <$> evaluateFull b

mkSink :: a -> IO (Behavior a, BehaviorSink a)
mkSink a = do
  aIORef <- newIORef a
  listeners <- newIORef []
  let sink = BehaviorSink aIORef listeners
  return (Sink sink, sink)

getSink :: BehaviorSink a -> IO a
getSink (BehaviorSink vIORef _) = readIORef vIORef

setSink :: BehaviorSink a -> a -> IO ()
setSink (BehaviorSink aIORef listenersRef) a = do
  listeners <- readIORef listenersRef
  writeIORef aIORef a
  forM_ listeners ($ a)

subscribeToAnyChange :: Behavior a -> IO () -> IO ()
subscribeToAnyChange (Sink (BehaviorSink _ lsIORef)) listener =
  modifyIORef lsIORef (const listener :)
subscribeToAnyChange (Lift1 _ b) listener = subscribeToAnyChange b listener
subscribeToAnyChange (Lift2 _ b c) listener = do
  subscribeToAnyChange b listener
  subscribeToAnyChange c listener

localActuate :: Behavior a -> (a -> IO ()) -> IO ()
localActuate b callback = do
  let update = callback =<< evaluate b
  subscribeToAnyChange b update
  update
{-
netActuateClient :: Int -> Behavior a -> IO ()
netActuateClient clientPort serverPort = undefined

netActuateServer :: Int -> Behavior a -> IO ()
netActuateServer serverPort = undefined

clientBehavior :: Behavior a
clientBehavior = undefined

serverBehavior :: Behavior a
serverBehavior = undefined
-}
