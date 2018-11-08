{-
# Netowking as a base for FRP
# Header
-}

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module M01_StaticNetwork where

import Safe
import Control.Monad.State
import Data.Proxy
import Data.Kind
import Data.Dynamic
import qualified Data.Graph as Graph
import qualified Data.Map as Map

import System.IO
import Control.Concurrent
import Control.Concurrent.Chan

{-
# Intro

This document attempts to build a framework of networking ideas that can be built apon to implement a distributed FRP network. This assumes:

* Nodes are all trusted and never fail.
* Connections between nodes are (in practice TCP can be used here):
    * Inorder
    * reliable (no packet loss nor data corruption)
    * have an expected small (on the order of less than a second) but unbounded delay.

We are concerned with how messages can be used and interpreted. All messages simply state a true fact about the "environment" $\Gamma$. When a node n receives a message i.e. a fact, they trust the sender node and add that fact to their knowlage base $\Sigma$. A node x for example can inform all other nodes that x0="Hello from x" by broadcasting that fact to all other nodes. It is important that nodes do not generate contradictory facts, but this can be solved by designating an "owner" of a variable in another variable $\omega_x$ for variable $x$. We'll need some place to start, so some rule must be hard coded into all nodes e.g. $\omega_genesis = NodeA$:

    Node n can assign variable $x$ iff $\omega_genesis = n$.

Implicitely, if a variable $\omega_x$ is not assigned, then it has no owner. It, and its corresponding variable can only be assigned by indering it from known facts.

## Time

Note that "variables" are immutable in the above scenario, but we can simulate mutable variables by using time-indexed variables. We likely choose to not time index correspoinding ownership variables (implying that the owner node is free to assign to a variable at all times).

We assume nodes have synchronized clocks. But these clocks should *only* be used to decide on new variable assignemt times. Dependant variables must change in 0 time! That is, when a node calculates a dependant value that it owns, it must do so for the time the value theoretically changed, and ignore the time it takes to calculate the dependant value.

## Infering Timely Facts

In an FRP setting, we usually want to infer a fact f at time t, that depends on the complete history of time indexed-variable x. How does a node know if the knowlage is complete?

    * If the local node owns the variable, then knowlage is complete.
    * else
        * We must design the protocol to ensure that complete information is received.
        * May need to send "heartbeats" to notify of no change.

# Static graph of behaviors

The structure of the circuit is known statically. Hence all $\omega$ variables can be hard coded. It is also statically known, which nodes require at info, and hence what data must be set over the network.
-}

data Circuit = Circuit
    { circGraph  :: Graph.Graph
    , circBehDyn :: Map.Map Graph.Vertex Dynamic -- Dynamic is a behavior or some type (can be infered from vertex)
    }

circBeh :: (Typeable owner, Typeable a)
        => Circuit -> BehaviorIx owner a -> Behavior owner a
circBeh c = flip fromDyn (error "Unexpected type of behavior.") . (circBehDyn c Map.!) . bixVert

newtype BehaviorIx (owner :: Node) a = BehaviorIx { bixVert :: Graph.Vertex }
data Behavior (owner :: Node) a where
    Source :: (Proxy (node :: Node))
           -> (Proxy (localInput :: LocalInput))
           -> Behavior node (LocalInputType localInput)
    Map :: (a -> b) -> BehaviorIx owner a -> Behavior owner b
    Ap  :: BehaviorIx owner (a -> b) -> BehaviorIx owner a -> Behavior owner b
    Send :: (Proxy (toNode :: Node))
         -> BehaviorIx fromNode a
         -> Behavior toNode a

-- Now we'd like a monad to build this circuit in
type Moment a = State MomentState a
data MomentState = MomentState
    { momentNextVert :: Graph.Vertex
    , momentBehDyn   :: Map.Map Graph.Vertex Dynamic
    , momentEdges    :: [Graph.Edge]
    }

beh :: (Typeable owner, Typeable a)
    => Behavior owner a -> Moment (BehaviorIx owner a)
beh b = do
    MomentState v bd es <- get
    let behIx = BehaviorIx v
    put $ MomentState
            -- Increment vertex index.
            (v+1)
            -- Add behavior to map.
            (Map.insert v (toDyn behIx) bd)
            -- Add eges.
            (((v,) <$> behDeps b) ++ es)
    return behIx
    where
        behDeps :: Behavior owner a -> [Graph.Vertex]
        behDeps (Source _ _) = []
        behDeps (Map _ b)    = [bixVert b]
        behDeps (Ap fb ib)   = [bixVert fb, bixVert ib]
        behDeps (Send _ b)   = [bixVert b]

buildCircuit :: Moment () -> Circuit
buildCircuit builder = Circuit graph behDyn
    where
        (_, MomentState nextVIx behDyn edges) = runState builder (MomentState 0 Map.empty [])
        graph = Graph.buildG (0, nextVIx - 1) edges


-- Lets make a simple calculator example with 3 clients and a server that we want to do that calculating.
data Node
    = ClientA
    | ClientB
    | ClientC
    | Server
    deriving (Eq, Ord)

-- The only local input we care about is key presses.
data LocalInput = Key
type family LocalInputType (a :: LocalInput) where
    LocalInputType Key = Char

calculatorCircuit :: Moment ()
calculatorCircuit = do
    aKeyB <- beh $ Source (Proxy @ClientA) (Proxy @Key)
    bKeyB <- beh $ Source (Proxy @ClientB) (Proxy @Key)
    cKeyB <- beh $ Source (Proxy @ClientC) (Proxy @Key)
    
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

data Msg -- TODO 
data Time -- TODO

actuate :: Node                        -- What node to run.
        -> Node                        -- Clock sync node
        -> IO Time                     -- Local clock
        -> Moment ()                   -- The circuit to build
        -> _localInputsChan            -- Local inputs
        -> Map.Map Node (Chan Msg, Chan Msg)   -- (send, receive) Chanels to other nodes
        -> IO ()
actuate myNode
        clockSyncNode
        getTime
        mkCircuit
        localInChan
        handles
  = do
    -- Clock synchronize with clockSyncNode if not myNode and wait for starting time. (TODO regularly synchronize clocks).
    -- Else accept clock sync with all other nodes, then braodcast a starting time (to start the circuit).
    _

    -- Gather Listeners (list of "on some behavior changed, perform some IO action")
    --    TODO allow IO listeners to be specified in the Moment monad and saved in the Circuit
    --    Add IO listeners for sending Msgs to other nodes.
    _

    -- A single change to compile all local inputs and messages from other nodes.
    inChan :: Chan _ <- newChan
    -- Listen for local inputs
    forkIO . forever $ do _
    -- Listen for messages from other nodes.
    forM_ (Map.assocs handles) $ \(otherNode, (sendChan, recvChan)) -> forkIO $ do _

    -- Thread that just processes inChan, keeps track of the whole circuit and
    -- decides what listeners to execute (sending them to listenersChan/msgChan).
    listenersChan :: Chan (IO ()) <- newChan
    outMsgChan :: Chan (Node, Msg) <- newChan
    forkIO _
        -- THIS IS WHERE ALL THE INTERESTING STUFF HAPPENS

    -- Thread that just executes listeners
    forkIO . forever . join . readChan $ listenersChan

    -- Thread that just sends messages to other nodes
    forkIO . forever $ do
        (toNode, msg) <- readChan outMsgChan
        writeChan (fst $ handles Map.! toNode) msg

    -- TODO some way to stop gracefully.
    
    return ()