{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}

module NFRP
    ( module FRP

    -- * Interfacing with the real world
    , NetworkSettings (..)
    , sourceEvents
    ) where
import           Control.Concurrent (forkIO, threadDelay)
import           Control.Concurrent.Chan
import           Control.Concurrent.MVar
import           Control.DeepSeq
import           Control.Monad (forM_)
import           Control.Monad.State
import           Data.Binary (Binary, encode, decode)
import qualified Data.ByteString.Lazy as BSL
import           Data.Int (Int64)
import qualified Data.Map as Map
import           Data.Map (Map, delete)
import           Network.Simple.TCP

import           FRP
import           ClockSync

data NetworkSettings
    = Default
    | SimulateLatency Int -- ^ micro seconds

-- | Create homogenious event input events for all nodes in a network. The event for this node
-- can be fired with the returned function. All other nodes' events are received via broadcast.
--
-- WARNING you should only do this once with inputs being all possible inputs. Doing this multiple
-- times will create multiple time deomains!
--
-- TODO actual clock synchronization
sourceEvents
    :: forall node input
    .  ( Eq node, Ord node, Bounded node, Enum node
       , Binary node, Binary input
       , NFData input
       )
    => NetworkSettings
    -> node
    -- ^ This node
    -> Map node (String, String)
    -- ^ (host, port) of nodes (Should be total including thisNode)
    -> IO ( (Maybe input) -> IO ()
          -- ^ Fire input event for this node (Or nothing to indicate a lack of events).
          , Map node (Event input)
          -- ^ Map from node to input events.
          )
sourceEvents networkSettings thisNode addresses = do
    -- Create source events for all nodes including this node.
    sourceEs :: Map node ([EventPart a] -> IO (), Event a)
        <- Map.fromList <$> (forM [minBound..maxBound] $ \ node -> (node,) <$> sourceEvent)
    let (fireLocalRaw, localInputE) = sourceEs Map.! thisNode

    -- Create send/receive chans with which to communicate with other nodes
    let otherNodeAddresses = delete thisNode addresses
    sendRecvChans :: Map node (Chan [EventPart input], Chan [EventPart input])
        <- forM otherNodeAddresses $ \ _ -> (,) <$> newChan <*> newChan
    let sendChans = fst <$> sendRecvChans
        recvChans = snd <$> sendRecvChans

    -- Broadcast local events to other nodes
    _ <- watchE localInputE $ \part -> forM_ sendChans (\sendChan -> writeChan sendChan [part])

    -- Fire events received by other nodes
    sequence_ $ flip Map.mapWithKey recvChans $ \otherNode recvChan
        -> let (fireOther, _) = sourceEs Map.! otherNode
            in forkIO $ forever (fireOther =<< readChan recvChan)

    -- Connect to other nodes asynchronously and hook up sendRecvChans.
    connectToOtherNodes networkSettings thisNode addresses sendRecvChans

    -- TODO Clock Sync

    -- Initialize this node's event with no events till time 0.
    localStartTime <- getLocalTime
    fireLocalRaw (listToPartialE Nothing (Just localStartTime) [])

    -- Create fire event function based on current time.
    lastFireTimeMVar <- newMVar localStartTime
    let fireLocal :: Maybe input -> IO ()
        fireLocal inputM = modifyMVar_ lastFireTimeMVar $ \ lastFireTime -> do
            t <- getLocalTime
            fireLocalRaw $ listToPartialE
                        (Just lastFireTime)
                        (Just t)
                        [(t, input) | Just input <- [inputM]]
            return t

    return $ (fireLocal, snd <$> sourceEs)

-- | Accepts connections to and from all other nodes. forwards messages in the
-- send chans to their corresponding nodes, and writes received messages to the
-- corresponding read chans.
connectToOtherNodes
    :: (Eq node, Ord node, Bounded node, Binary node, Binary input)
    => NetworkSettings
    -> node
    -- ^ This node
    -> Map node (String, String)
    -- ^ (host, port) Should be total including this node.
    -> Map node (Chan [EventPart input], Chan [EventPart input])
    -- ^ Send and receive Chans (Should be total excluding this node)
    -> IO ()
connectToOtherNodes networkSettings thisNode addresses sendRecvChans = do

    -- PROTOCOL:
    --
    -- Notes:
    --
    --   * Act as a TCP server for all (Ord) lesser users, and as a client for
    --     all greater nodes
    --   * All messages are prefixed with an Int32 length in bytes of the
    --     message.
    --
    -- On Connection:
    --
    --   1. The 2 nodes send a their node (e.g. Player1) to identify themselves.
    --      * TODO we could maybe infer this from the addresses map and SockAddr.
    --   2. Nodes forever send messages from the send chans (these should be
    --      event parts of their input events).

    -- TCP server (connecting to lower nodes).
    when (thisNode /= minBound) $ do
        let (thisHost, thisPort) = addresses Map.! thisNode
        _ <- forkIO $ serve (Host thisHost) thisPort onConnection
        return ()

    -- Connect to higher nodes (TCP client).
    sequence_ $ flip Map.mapWithKey addresses $ \ otherNode (otherHost, otherPort) ->
        when (otherNode > thisNode) $ void $ forkIO $
            -- TODO retry (will this fail if server is not yet started?)
            connect otherHost otherPort onConnection

    where
    enc a = let encodedA = encode a
                size :: Int64
                size = BSL.length encodedA
            in encode size <> encodedA
    send' :: Binary a => Socket -> a -> IO ()
    send' = case networkSettings of
        Default -> \socket a ->
            sendLazy socket (enc a)
        SimulateLatency l -> \socket a -> void $ forkIO $ do
            threadDelay l
            sendLazy socket (enc a)

    recv' :: Binary a => Socket -> IO a
    recv' socket = do
        Just sizeBS <- recv socket 8
        let size :: Int64
            size = decode $ BSL.fromStrict sizeBS
        Just aBS <- recv socket (fromIntegral size)
        return $ decode $ BSL.fromStrict aBS



    onConnection :: (Socket, SockAddr) -> IO ()
    onConnection (socket, _sockAddr) = do
        -- Identify eachother (Make sure to send first else wel'll deadlock).
        send' socket thisNode
        otherNode <- recv' socket

        -- Send/receive loop
        let (sendChan, recvChan) = sendRecvChans Map.! otherNode
        _ <- forkIO $ forever $ send' socket =<< readChan sendChan
        forever $ writeChan recvChan =<< recv' socket
