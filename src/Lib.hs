{-# LANGUAGE ExistentialQuantification #-}

module Lib where

data Behavior a
  = Poll (IO a)
  | forall b. Lift1 (b -> a)
                    (Behavior b)
  | forall c b. Lift2 (b -> c -> a)
                      (Behavior b)
                      (Behavior c)

evaluate :: Behavior a -> IO a
evaluate (Poll poll) = poll
evaluate (Lift1 f b) = f <$> evaluate b
evaluate (Lift2 f b c) = f <$> evaluate b <*> evaluate c

localActuate :: Behavior a -> (a -> IO ()) -> IO ()
localActuate beh callback = do
  callback =<< evaluate beh
  localActuate beh callback

netActuateClient :: Int -> Behavior a -> IO ()
netActuateClient clientPort serverPort = undefined

netActuateServer :: Int -> Behavior a -> IO ()
netActuateServer serverPort = undefined

clientBehavior :: Behavior a
clientBehavior = undefined

serverBehavior :: Behavior a
serverBehavior = undefined
