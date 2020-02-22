{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}

module NFRP
    ( Behavior
    , Event
    , never
    , once

    -- * Combinators
    , step
    , stepI
    -- , leftmost

    -- * Interfacing with the real world
    , sourceEvents
    ) where
import           Control.Concurrent (forkIO)
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
import           Data.Time.Clock.System
import           Network.Simple.TCP

import           GateRep
import           Time


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
    => node
    -- ^ This node
    -> Map node (String, String)
    -- ^ (host, port) of nodes (Should be total including thisNode)
    -> IO ( (Maybe input) -> IO ()
          -- ^ Fire input event for this node (Or nothing to indicate a lack of events).
          , Map node (Event input)
          -- ^ Map from node to input events.
          )
sourceEvents thisNode addresses = do
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
    connectToOtherNodes thisNode addresses sendRecvChans

    -- TODO Clock Sync

    -- Initialize this node's event with no events till time 0.
    localStartTime <- currentIntegerTime
    fireLocalRaw (listToEPartsExcInc Nothing (Just localStartTime) [])

    -- Create fire event function based on current time.
    lastFireTimeMVar <- newMVar localStartTime
    let fireLocal :: Maybe input -> IO ()
        fireLocal inputM = modifyMVar_ lastFireTimeMVar $ \ lastFireTime -> do
            t <- currentIntegerTime
            fireLocalRaw $ listToEPartsExcInc
                        (Just lastFireTime)
                        (Just t)
                        [(t, input) | Just input <- [inputM]]
            return t

    return $ (fireLocal, snd <$> sourceEs)

-- | Get the current system time in nanoseconds
currentIntegerTime :: IO Time
currentIntegerTime = do
    MkSystemTime s ns <- getSystemTime
    let si  = fromIntegral s
        nsi = fromIntegral ns
    return (si * (10^(9 :: Int)) + nsi)


-- | Accepts connections to and from all other nodes. forwards messages in the
-- send chans to their corresponding nodes, and writes received messages to the
-- corresponding read chans.
connectToOtherNodes
    :: (Eq node, Ord node, Bounded node, Binary node, Binary input)
    => node
    -- ^ This node
    -> Map node (String, String)
    -- ^ (host, port) Should be total including this node.
    -> Map node (Chan [EventPart input], Chan [EventPart input])
    -- ^ Send and receive Chans (Should be total excluding this node)
    -> IO ()
connectToOtherNodes thisNode addresses sendRecvChans = do

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
    sequence_ $ flip Map.mapWithKey addresses $ \ otherNode (otherHost, otherPort) -> do
        when (otherNode > thisNode) $ void $ forkIO $
            -- TODO retry (will this fail if server is not yet started?)
            connect otherHost otherPort onConnection

    where
    send' :: Binary a => Socket -> a -> IO ()
    send' socket a = do
        let encodedA = encode a
            size :: Int64
            size = BSL.length encodedA
        sendLazy socket (encode size <> encodedA)

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


{-

# Delays
We want to allow a primitive delay type, but only for behaviors, as delaying behaviors (I think) cannot cause
a delayed event. A delay is infinitly small so an event cannot occur between a behaior change and it's delayed
behavior's change, hence nothing can change the behavior again so we have:

    delay (delay myBeh) == delay myBeh

TODO formailize this above!
Sketch: events are only caused by other events (or source events), so if we only alow delaying behaviors,
then there is no way to delay events.

-}

{-
heartbeatFeq :: Int
heartbeatFeq = 1 -- per second

data Responsibility node ctx
    -- | When maxT increases for a behavior do some IO.
    = forall a . OnPossibleChange
            node    -- ^ Which node's responsibility is this.
            (BehaviorIx a)
            Bool    -- ^ Is it a local listerner? As opposed to sending a msg to another node.
            (ctx -> BMap a -> IO ())
    -- TODO Event based responsibility

instance Show node => Show (Responsibility node localCtx) where
    show (OnPossibleChange node bix isLocal _)
        = "OnPossibleChange "
        ++ show node
        ++ " ("
        ++ show bix
        ++ ") "
        ++ show isLocal
        ++ " _"

data InChanData
    = InChan_Heartbeat
    | forall a . InChan_LocalUpdate (EventIx a) a
    | InChan_RemoteUpdate [UpdateList]

actuate :: forall node ctx mkCircuitOut
        .  (NodeC node)
        => ctx
        -> node                -- What node to run.
        -> node                -- Clock sync node
        -> IO Time                     -- Local clock
        -> Moment (MomentTypes node ctx) mkCircuitOut         -- The circuit to build
        -> Map.Map node (Chan [UpdateList], Chan [UpdateList])
                                       -- (send, receive) Chanels to other nodes
        -> IO ( IO ()               -- IO action that stops the actuation
              , mkCircuitOut                   -- Result of building the circuit
              , EventInjector node  -- Event injector for the actuated node
                                    -- ^ function to inject events
              , IO Time             -- ^ adjusted local time.
              )
actuate ctx
        myNode
        _clockSyncNode
        getLocalTime
        mkCircuit
        channels
  = do

    (stop, readStop) <- do
        c <- newChan
        return (writeChan c (), readChan c)

    let readUntillStop :: Chan a -> (a -> IO ()) -> IO ()
        readUntillStop c f = fix $ \ loop -> do
            e <- race readStop (readChan c)
            case e of
                Left () -> return ()
                Right v -> f v >> loop

    let (circuit, listeners, mkCircuitOut) = buildCircuit mkCircuit

        enableLog = True

        putLog :: String -> IO ()
        putLog str = when enableLog $ putStrLn $ "\033[34" ++ show myNode ++ "\033[0m: " ++ str

    -- Clock synchronize with clockSyncNode if not myNode and wait for starting time. (TODO regularly synchronize clocks).
    -- Else accept clock sync with all other nodes, then braodcast a starting time (to start the circuit).
    let getTime = trace "TODO create node wide synchronized getTime function" getLocalTime

    -- Gather Responsabilities (list of "on some behavior changed, perform some IO action")
    let myResponsabilitiesListeners :: [Responsibility node ctx]
        myResponsabilitiesListeners
            = mapMaybe (\ l -> case l of
                Listener listenerNode bix handler
                    | listenerNode == myNode
                    -> Just $ OnPossibleChange
                                myNode
                                bix
                                True
                                (\ctx' bmap -> case headBMap bmap of
                                    Just (maxT, val) -> handler ctx' val maxT
                                    Nothing -> return ()
                                    )
                _   -> Nothing)
            $ listeners

        myResponsabilitiesMessage :: [Responsibility node ctx]
        myResponsabilitiesMessage
            = mapMaybe (\(GateIx' g) -> case g of
                GateIxB bix -> case circBeh circuit bix of
                    SendB fromNode toNodes _bix
                        | fromNode == myNode
                        -> Just $ OnPossibleChange myNode bix False
                            (\ _ bmap -> let
                                toNodes' = filter (/= myNode) $ case toNodes of
                                    All     -> Map.keys channels
                                    Some ns -> ns
                                in forM_ toNodes' $ \ toNode -> let
                                        sendChan = fst (channels Map.! toNode)
                                        in do
                                            putLog "Sending updates"
                                            writeChan sendChan [UpdateListB bix bmap]
                            )
                    _ -> Nothing
                GateIxE eix -> case circEvt circuit eix of
                    SendE {} -> error "TODO support sending events" -- Just $ OnEvent bix False _doSend
                    _ -> Nothing
                )
            $ Map.elems (circGateIxs circuit)

        allSourceEvts :: [EventIx']
        allSourceEvts
            = mapMaybe (\(GateIx' g) -> case g of
                GateIxB _   -> Nothing
                GateIxE eix -> Just (EventIx' eix)
                )
            $ Map.elems (circGateIxs circuit)

        -- My node's responsabilities
        responsabilities :: [Responsibility node ctx]
        responsabilities = myResponsabilitiesMessage ++ myResponsabilitiesListeners

    putLog $ show myResponsabilitiesListeners ++ " my listener responsabilities"
    putLog $ show (length $ circGateIxs circuit) ++ " gates"
    putLog $ show myResponsabilitiesMessage ++ " my message responsabilities"

    -- A single change to compile all local inputs and messages from other nodes.
    inChan :: Chan InChanData <- newChan

    -- Listen for local inputs (time is assigned here)
    let injectInput :: EventInjector node
        injectInput = EventInjector myNode $ \ (SourceEvent myNodeSE eix) valA -> do
            when (myNode /= myNodeSE) (error $ "EventInjector and SourceEvent have different nodes: "
                                            ++ show myNode ++ " and " ++ show myNodeSE)
            writeChan inChan (InChan_LocalUpdate eix valA)

    -- Listen for messages from other nodes.
    _asRcv <- forM (Map.assocs channels) $ \(_otherNode, (_, recvChan)) -> forkIO
        . readUntillStop recvChan $ \ recvVal -> do
            writeChan inChan (InChan_RemoteUpdate recvVal)
            putLog ("received input: " ++ show recvVal)

    -- Heartbeat
    _aHrtbt <- let loop = do
                        e <- race
                                readStop
                                (threadDelay (1000000 `div` heartbeatFeq))
                        case e of
                            Left () -> return ()
                            Right _ -> do
                                writeChan inChan InChan_Heartbeat
                                loop
                    in forkIO loop

    -- Thread that just processes inChan, keeps track of the whole circuit and
    -- decides what listeners to execute (sending them to changesChan).
    let (circuit0, initialUpdates) = mkLiveCircuit myNode circuit :: (LiveCircuit node, [UpdateList])
    changesChan :: Chan [UpdateList] <- newChan
    writeChan changesChan initialUpdates
    _aLiveCircuit <- do
        liveCircuitRef <- newIORef circuit0
        forkIO . readUntillStop inChan $ \ inChanData -> do
            -- Update state: Calculate for each behavior what is known and up to what time
            oldLiveCircuit <- readIORef liveCircuitRef
            let eixMinT :: _
                eixMinT eix = case lcEvtMaxT oldLiveCircuit eix of
                                Just (DI_JustAfter _)
                                    -> error $ "Live circuit has an event maxT of \"DI_JustAfter\"."
                                            ++ " This should not happen as we do not allow delaying events."
                                Just DI_Inf
                                    -> error "Got an event update even though maxT is already infinity"
                                -- No data yet. This is the first event update so minT is 0
                                Nothing -> DI_Exactly 0
                                -- We have data up to time t, so
                                Just (DI_Exactly t) -> DI_JustAfter t
            updates <- case inChanData of
                InChan_RemoteUpdate ups -> return ups
                InChan_LocalUpdate eix valA -> do
                    time <- getTime
                    return [UpdateListE eix (spanEMap (Just (eixMinT eix))
                                                      [(time, valA)]
                                                      (Just (DI_JustAfter time))
                                            )]
                        -- toTime time) [(toTime time, valA)] (eixMinT eix)]
                InChan_Heartbeat -> do
                    time <- getTime
                    return $ map
                        (\ (EventIx' eix) -> UpdateListE eix
                                (spanEMap (Just (eixMinT eix))
                                []
                                (Just (DI_JustAfter time)))
                        )
                        allSourceEvts
            putLog $ "Got inChan updates for " ++ show updates
            let (newLiveCircuit, changes) = lcTransaction oldLiveCircuit updates
            putLog $ "Changes from lcTransaction: " ++ show changes
            writeIORef liveCircuitRef newLiveCircuit
            writeChan changesChan changes

    -- Fullfill responsibilities: Listeners + sending to other nodes
    listenersChan :: Chan (IO ()) <- newChan
    outMsgChan :: Chan (IO ()) <- newChan
    _aResponsibilities <- forkIO . readUntillStop changesChan $ \ changes -> do
        putLog $ "Got changesChan with changes: " ++ show changes
        forM_ responsabilities $
            \ (OnPossibleChange respNode bix isLocalListener action) ->
                -- TODO double forM_ is inefficient... maybe index changes on BehaviorIx?
                when (respNode == myNode) $ forM_ changes $ \ case
                    UpdateListB bix' bmap
                        -- | Just Refl <- eqT @(BehaviorIx bixO bixA) @(BehaviorIx bixO' bixA')
                        | bixVert bix == bixVert bix'
                        -> do
                            putLog $ "Found listener for bix: " ++ show bix
                            writeChan
                                (if isLocalListener then listenersChan else outMsgChan)
                                (action ctx (unsafeCoerce bmap))
                            putLog $ "Sent listener action for bix: " ++ show bix

                    -- Note we don't support Event listeners (yet).
                    _ -> return ()

    -- Thread that just executes listeners
    _aListeners <- forkIO $ readUntillStop listenersChan id

    -- Thread that just sends mesages to other nodes
    _aMsg <- forkIO $ readUntillStop outMsgChan id

    -- TODO some way to stop gracefully.

    putLog "Started all threads."

    return (stop, mkCircuitOut, injectInput, getTime)
-}