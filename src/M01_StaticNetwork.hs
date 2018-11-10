
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

module M01_StaticNetwork where

import Safe
import Control.Monad.State
import Unsafe.Coerce
import Data.IORef
import Data.Proxy
import Data.Kind
import Data.Dynamic
import Data.Maybe (fromMaybe, mapMaybe)
import Data.List (find, intersect)
import qualified Data.Graph as Graph
import qualified Data.Map as Map

import System.IO
import Control.Concurrent
import Control.Concurrent.Chan

data Circuit = Circuit
    { circGraph  :: Graph.Graph
    , circBehDyn :: Map.Map Graph.Vertex Dynamic -- Dynamic is a behavior or some type (can be infered from vertex)
    , circAllBeh :: [BehaviorIx']
    }

circBeh :: forall (owner :: Node) a . (Typeable owner, Typeable a)
        => Circuit -> BehaviorIx owner a -> Behavior owner a
circBeh c = flip fromDyn (error "Unexpected type of behavior.") . (circBehDyn c Map.!) . bixVert

newtype BehaviorIx (owner :: Node) (a :: Type) = BehaviorIx { bixVert :: Graph.Vertex }
        deriving (Eq, Ord)
data Behavior (owner :: Node) (a :: Type) where
    Source :: (Typeable node)
           => (Proxy node)
           -> Behavior node LocalInput
    Map :: (Typeable owner, Typeable a, Typeable b)
        => (a -> b) -> BehaviorIx owner a -> Behavior owner b
    Ap  :: (Typeable owner, Typeable a, Typeable b)
        => BehaviorIx owner (a -> b) -> BehaviorIx owner a -> Behavior owner b
    Send :: (Typeable fromNode, Typeable toNode, Typeable a)
         => (Proxy toNode)
         -> BehaviorIx fromNode a
         -> Behavior toNode a

-- Now we'd like a monad to build this circuit in
type Moment a = State MomentState a
data MomentState = MomentState
    { momentNextVert :: Graph.Vertex
    , momentBehDyn   :: Map.Map Graph.Vertex Dynamic
    , momentEdges    :: [Graph.Edge]
    , momentAllBehs  :: [BehaviorIx']
    }

beh :: (Typeable owner, Typeable a)
    => Behavior owner a -> Moment (BehaviorIx owner a)
beh b = do
    MomentState v bd es allBehs<- get
    let behIx = BehaviorIx v
    put $ MomentState
            -- Increment vertex index.
            (v+1)
            -- Add behavior to map.
            (Map.insert v (toDyn behIx) bd)
            -- Add eges and behavior.
            (((v,) <$> behDepVerts b) ++ es)
            (BehaviorIx' behIx : allBehs)
    return behIx
        
behDepVerts :: Behavior owner a -> [Graph.Vertex]
behDepVerts (Source _)   = []
behDepVerts (Map _ b)    = [bixVert b]
behDepVerts (Ap fb ib)   = [bixVert fb, bixVert ib]
behDepVerts (Send _ b)   = [bixVert b]

data BehaviorIx' = forall (o :: Node) (a :: Type) . (Typeable o, Typeable a) => BehaviorIx' (BehaviorIx o a)
instance Eq BehaviorIx' where
    (BehaviorIx' (BehaviorIx v1)) == (BehaviorIx' (BehaviorIx v2)) = v1 == v2

behDeps :: (Typeable owner, Typeable a) => Behavior owner a -> [BehaviorIx']
behDeps (Source _)   = []
behDeps (Map _ b)    = [BehaviorIx' b]
behDeps (Ap fb ib)   = [BehaviorIx' fb, BehaviorIx' ib]
behDeps (Send _ b)   = [BehaviorIx' b]

buildCircuit :: Moment () -> Circuit
buildCircuit builder = Circuit graph behDyn allBehs
    where
        (_, MomentState nextVIx behDyn edges allBehs) = runState builder (MomentState 0 Map.empty [] [])
        graph = Graph.buildG (0, nextVIx - 1) edges


-- Lets make a simple calculator example with 3 clients and a server that we want to do that calculating.
data Node
    = ClientA
    | ClientB
    | ClientC
    | Server
    deriving (Eq, Ord)

class SingNode (node :: Node) where singNode :: Proxy node -> Node
instance SingNode ClientA where singNode _ = ClientA
instance SingNode ClientB where singNode _ = ClientB
instance SingNode ClientC where singNode _ = ClientC
instance SingNode Server where singNode _ = Server

-- The only local input we care about is key presses.
type LocalInput = Char

calculatorCircuit :: Moment ()
calculatorCircuit = do
    aKeyB <- beh $ Source (Proxy @ClientA)
    bKeyB <- beh $ Source (Proxy @ClientB)
    cKeyB <- beh $ Source (Proxy @ClientC)
    
    leftB  <- beh =<< Send (Proxy @Server) <$> readIntB aKeyB
    rightB <- beh =<< Send (Proxy @Server) <$> readIntB cKeyB
    opB    <- beh =<< Send (Proxy @Server) <$> (beh $ Map (\case
                            '+' -> (+)
                            '/' -> div
                            '*' -> (*)
                            _   -> (-) :: (Int -> Int -> Int)) 
                        bKeyB)

    resultB_ <- beh $ opB `Ap` leftB
    resultB  <- beh $ resultB_ `Ap` rightB

    return ()

    where
        readIntB :: Typeable o
                 => BehaviorIx o Char -> Moment (BehaviorIx o Int)
        readIntB = beh . Map (\c -> readDef 0 [c])

type Time = Int -- TODO Int64? nanoseconds?

actuate :: forall (myNode :: Node)
        .  (SingNode myNode)
        => Proxy myNode                        -- What node to run.
        -> Node                        -- Clock sync node
        -> IO Time                     -- Local clock
        -> Moment ()                   -- The circuit to build
        -> Chan LocalInput             -- Local inputs
        -> Map.Map Node (Chan (Time, [Update]), Chan (Time, [Update]))   -- (send, receive) Chanels to other nodes
        -> IO ()
actuate myNodeProxy
        clockSyncNode
        getLocalTime
        mkCircuit
        localInChan
        handles
  = do
    let myNode = singNode myNodeProxy
        circuit = buildCircuit mkCircuit

    -- Clock synchronize with clockSyncNode if not myNode and wait for starting time. (TODO regularly synchronize clocks).
    -- Else accept clock sync with all other nodes, then braodcast a starting time (to start the circuit).
    let getTime = error "TODO create synchronized getTime function" :: IO Time

    -- Gather Listeners (list of "on some behavior changed, perform some IO action")
    --    TODO allow IO listeners to be specified in the Moment monad and saved in the Circuit
    --    Add IO listeners for sending Msgs to other nodes.
    let responsabilities = error "TODO" :: [Responsibility myNode]

    -- Get all source behaviors for this node.
    let mySourceBs :: [BehaviorIx myNode LocalInput]
        mySourceBs = flip mapMaybe (circAllBeh circuit) (\(BehaviorIx' (b :: Behavior bo ba)) -> _filterBeh b)

    -- A single change to compile all local inputs and messages from other nodes.
    inChan :: Chan (Time, [Update]) <- newChan

    -- Listen for local inputs (time is assigned here)
    _ <- forkIO . forever $ do
        input <- readChan localInChan
        time <- getTime
        writeChan inChan (time, [Update b input | b <- mySourceBs])

    -- Listen for messages from other nodes.
    forM_ (Map.assocs handles) $ \(otherNode, (_, recvChan)) -> forkIO
        $ writeChan inChan =<< readChan recvChan

    -- Thread that just processes inChan, keeps track of the whole circuit and
    -- decides what listeners to execute (sending them to listenersChan/msgChan).
    listenersChan :: Chan (IO ()) <- newChan
    outMsgChan :: Chan (IO ()) <- newChan
    liveCircuitRef <- newIORef (mkLiveCircuit circuit)
    _ <- forkIO . forever $ do
        -- Update state: Calculate for each behavior what is known and up to what time
        (time, updates) <- readChan inChan
        oldLiveCircuit <- readIORef liveCircuitRef
        let (newLiveCircuit, changedBehs) = lcTransaction oldLiveCircuit time updates
        writeIORef liveCircuitRef newLiveCircuit

        -- Fullfill responsibilities
        forM_ responsabilities $ \(OnPossibleChange b isLocalListener action) -> 
            when ((BehaviorIx' b) `elem` changedBehs)
                (writeChan (if isLocalListener then listenersChan else outMsgChan) action)

    -- Thread that just executes listeners
    _ <- forkIO . forever . join . readChan $ listenersChan

    -- Thread that just sends messages to other nodes
    _ <- forkIO . forever . join . readChan $ outMsgChan

    -- TODO some way to stop gracefully.
    
    return ()


data LiveCircuit = LiveCircuit
    { lcCircuit :: Circuit
    , lcBehMaxT :: forall (owner :: Node) a . (Typeable owner, Typeable a) => BehaviorIx owner a -> Time       -- Up to what time is the value of a behabior known.
    , lcBehVal  :: forall (owner :: Node) a . (Typeable owner, Typeable a) => Time -> BehaviorIx owner a -> Maybe a  -- Value of a behavior at a time. Time must be <= lcBehMaxT else Nothing.
    }

mkLiveCircuit :: Circuit -> LiveCircuit
mkLiveCircuit c = LiveCircuit
    { lcCircuit     = c
    , lcBehMaxT     = const 0
    , lcBehVal      = (\t b -> if t /= 0 then lcBehValTimeError else error "TODO initial value") -- TODO this is just a hack default value
    }

lcBehValTimeError = error "Attempt to access behavior value outside of known time."

data Update = forall owner a . Update (BehaviorIx owner a) a

data Responsibility (responsibleNode :: Node)
    = forall (owner :: Node) a . (Typeable owner, Typeable a) => 
        OnPossibleChange
            (BehaviorIx owner a)
            Bool    -- ^ Is it a local listerner? As opposed to sending a msg to another node.
            (IO ())

-- Transactionally update the circuit. Returns (_, changed behaviors (lcBehMaxT has increased))
lcTransaction :: LiveCircuit -> Time -> [Update] -> (LiveCircuit, [BehaviorIx'])
lcTransaction lc t ups = (LiveCircuit
    { lcCircuit     = c
    , lcBehMaxT     = lcBehMaxT'
    , lcBehVal      = lcBehVal'
    }, error "TODO calculate changed behaviors")
    where
        c = lcCircuit lc

        lcBehMaxT' :: forall (owner :: Node) (a :: Type) . (Typeable owner, Typeable a)
                   => BehaviorIx owner a -> Time
        lcBehMaxT' b@(BehaviorIx v) = case find (\(Update (BehaviorIx v') _) -> v == v') ups of
            -- Is updated in this transaction, so use transaction time.
            Just _ -> t
            -- Else use min of dependants. If no dependants, then no change.
            Nothing -> let
                deps = behDeps $ circBeh c b
                in if null deps
                    then lcBehMaxT lc b -- No change
                    else minimum $ (\(BehaviorIx' b') -> lcBehMaxT' b') <$> deps

        -- TODO/NOTE this is super inefficient
        lcBehVal' :: forall (owner :: Node) a . (Typeable owner, Typeable a)
                 => Time -> BehaviorIx owner a -> Maybe a
        lcBehVal' t' b@(BehaviorIx v)
            | t' > lcBehMaxT' b  = Nothing
            | otherwise          = case find (\(Update (BehaviorIx v') _) -> v == v') ups of
                -- Is updated in this transaction, so use transaction value.
                -- TODO can we get rid of the unsafeCoerce here? We know the type is correct
                Just (Update _ val) -> unsafeCoerce $ Just val
                -- Else use min of dependants. If no dependants, then no change.
                Nothing -> case circBeh c b of
                    -- Nothing for source even if it is local, because we will get this as a transaction later any way.
                    Source _   -> Nothing
                    Map f bA    -> f <$> lcBehVal' t' bA
                    Ap fb ib   -> lcBehVal' t' fb <*> lcBehVal' t' ib
                    Send _ bA   -> lcBehVal' t' bA

