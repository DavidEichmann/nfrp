{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

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
import Data.Typeable (cast)
import Data.IORef
import Data.Proxy
import Data.Kind
import Data.Dynamic
import Data.Maybe (fromJust, mapMaybe)
import Data.List (find)
import qualified Data.Graph as Graph
import qualified Data.Map as Map

import Control.Concurrent

import Debug.Trace
-- import Control.Exception.Base (assert)

data GateIx' = forall (o :: Node) (a :: Type) . (Typeable o, Typeable a) => GateIx' (GateIx o a)
data GateIx (owner :: Node) (a :: Type) = GateIxB (BehaviorIx owner a) | GateIxE (EventIx owner a)

data BehaviorIx' = forall (o :: Node) (a :: Type) . (Typeable o, Typeable a) => BehaviorIx' (BehaviorIx o a)
newtype BehaviorIx (owner :: Node) (a :: Type) = BehaviorIx { bixVert :: Graph.Vertex }
        deriving (Eq, Ord)
data Behavior (owner :: Node) (a :: Type) where
    Step :: (Typeable owner, Typeable a)
        => a -> EventIx owner a -> Behavior owner a
    MapB :: (Typeable owner, Typeable a, Typeable b)
        => (a -> b) -> BehaviorIx owner a -> Behavior owner b
    Ap  :: (Typeable owner, Typeable a, Typeable b)
        => BehaviorIx owner (a -> b) -> BehaviorIx owner a -> Behavior owner b
    SendB :: (Typeable fromNode, Typeable toNode, Typeable a)
         => (Proxy toNode)
         -> BehaviorIx fromNode a
         -> Behavior toNode a
data EventIx' = forall (o :: Node) (a :: Type) . (Typeable o, Typeable a) => EventIx' (EventIx o a)
newtype EventIx (owner :: Node) (a :: Type) = EventIx { eixVert :: Graph.Vertex }
        deriving (Eq, Ord)
data Event (owner :: Node) (a :: Type) where
    Source :: (Typeable node)
        => (Proxy node)
        -> Event node LocalInput
    MapE :: (Typeable owner, Typeable a, Typeable b)
        => (a -> b) -> EventIx owner a -> Event owner b
    Sample :: (Typeable owner, Typeable a, Typeable b, Typeable c)
        => (a -> b -> c) -> BehaviorIx owner a -> EventIx owner b -> Event owner c
    SendE :: (Typeable fromNode, Typeable toNode, Typeable a)
        => (Proxy toNode)
        -> EventIx fromNode a
        -> Event toNode a


data Circuit = Circuit
    { circGraph    :: Graph.Graph
    , circGateDyn  :: Map.Map Graph.Vertex Dynamic
                    -- ^Dynamic is a Behavior or Event of some owner/type (can be infered from vertex)
    , circAllGates :: [GateIx']
    }
    
circBeh :: forall (owner :: Node) a . (Typeable owner, Typeable a)
        => Circuit -> BehaviorIx owner a -> Behavior owner a
circBeh c = flip fromDyn (error "Unexpected type of behavior.") . (circGateDyn c Map.!) . bixVert

circEvt :: forall (owner :: Node) a . (Typeable owner, Typeable a)
        => Circuit -> EventIx owner a -> Event owner a
circEvt c = flip fromDyn (error "Unexpected type of event.") . (circGateDyn c Map.!) . eixVert

data LiveCircuit = LiveCircuit
    { lcCircuit :: Circuit
    , lcGateMaxT :: forall (owner :: Node) a . (Typeable owner, Typeable a) => GateIx owner a -> Time
                    -- ^ Up to what time is the value of a behavior known OR
                    --   Up to what time are all events occorences known
    , lcBehVal  :: forall (owner :: Node) a . (Typeable owner, Typeable a) => Time -> BehaviorIx owner a -> Maybe a
                    -- ^ Value of a behavior at a time. Time must be <= lcBehMaxT else Nothing.
    , lcEvents  :: forall (owner :: Node) a . (Typeable owner, Typeable a) => EventIx owner a -> [(Time, a)]
                    -- ^ Complete events up to lcGateMaxT time in reverse chronological order.
    }

instance Eq BehaviorIx' where
    (BehaviorIx' (BehaviorIx v1)) == (BehaviorIx' (BehaviorIx v2)) = v1 == v2

-- Now we'd like a monad to build this circuit in
type Moment a = State MomentState a
data MomentState = MomentState
    { momentNextVert :: Graph.Vertex
    , momentBehDyn   :: Map.Map Graph.Vertex Dynamic
    , momentEdges    :: [Graph.Edge]
    , momentAllGates :: [GateIx']
    }

data Update = forall owner a . (Typeable owner, Typeable a)
                => UpdateB (BehaviorIx owner a) a
            | forall owner a . (Typeable owner, Typeable a)
                => UpdateE (EventIx    owner a) a

data Responsibility (responsibleNode :: Node)
    = forall (owner :: Node) a . (Typeable owner, Typeable a) => 
        OnPossibleChange
            (BehaviorIx owner a)
            Bool    -- ^ Is it a local listerner? As opposed to sending a msg to another node.
            (IO ())

beh :: (Typeable owner, Typeable a)
    => Behavior owner a -> Moment (BehaviorIx owner a)
beh b = do
    MomentState v bd es allGates <- get
    let behIx = BehaviorIx v
    put $ MomentState
            -- Increment vertex index.
            (v+1)
            -- Add behavior to map.
            (Map.insert v (toDyn behIx) bd)
            -- Add eges and behavior.
            (((v,) <$> behDepVerts b) ++ es)
            (GateIx' (GateIxB behIx) : allGates)
    return behIx

evt :: (Typeable owner, Typeable a)
    => Event owner a -> Moment (EventIx owner a)
evt e = do
    MomentState v bd es allGates <- get
    let evtIx = EventIx v
    put $ MomentState
            -- Increment vertex index.
            (v+1)
            -- Add event to map.
            (Map.insert v (toDyn evtIx) bd)
            -- Add eges and event.
            (((v,) <$> evtDepVerts e) ++ es)
            (GateIx' (GateIxE evtIx) : allGates)
    return evtIx
        
behDepVerts :: Behavior owner a -> [Graph.Vertex]
behDepVerts (Step _ e)    = [eixVert e]
behDepVerts (MapB _ b)    = [bixVert b]
behDepVerts (Ap fb ib)    = [bixVert fb, bixVert ib]
behDepVerts (SendB _ b)   = [bixVert b]

behDeps :: (Typeable owner, Typeable a) => Behavior owner a -> [GateIx']
behDeps (Step _ e)    = [GateIx' (GateIxE e)]
behDeps (MapB _ b)    = [GateIx' (GateIxB b)]
behDeps (Ap fb ib)    = [GateIx' (GateIxB fb), GateIx' (GateIxB ib)]
behDeps (SendB _ b)   = [GateIx' (GateIxB b)]
    
evtDepVerts :: Event owner a -> [Graph.Vertex]
evtDepVerts (Source _)     = []
evtDepVerts (MapE _ e)     = [eixVert e]
evtDepVerts (Sample _ b e) = [bixVert b, eixVert e]
evtDepVerts (SendE _ e)    = [eixVert e]

evtDeps :: (Typeable owner, Typeable a) => Event owner a -> [GateIx']
evtDeps (Source _)     = []
evtDeps (MapE _ e)     = [GateIx' (GateIxE e)]
evtDeps (Sample _ b e) = [GateIx' (GateIxB b), GateIx' (GateIxE e)]
evtDeps (SendE _ e)    = [GateIx' (GateIxE e)]

gateIxDeps :: (Typeable owner, Typeable a) => Circuit -> GateIx owner a -> [GateIx']
gateIxDeps c (GateIxB bix) = behDeps $ circBeh c bix
gateIxDeps c (GateIxE eix) = evtDeps $ circEvt c eix

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
    aKeyB <- (beh . (Step '0')) =<< (evt $ Source (Proxy @ClientA))
    bKeyB <- (beh . (Step '+')) =<< (evt $ Source (Proxy @ClientB))
    cKeyB <- (beh . (Step '0')) =<< (evt $ Source (Proxy @ClientC))
    
    leftB  <- beh =<< SendB (Proxy @Server) <$> readIntB aKeyB
    rightB <- beh =<< SendB (Proxy @Server) <$> readIntB cKeyB
    opB    <- beh =<< SendB (Proxy @Server) <$> (beh $ MapB (\case
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
        readIntB = beh . MapB (\c -> readDef 0 [c])

type Time = Int -- TODO Int64? nanoseconds?

actuate :: forall (myNode :: Node)
        .  (Typeable myNode, SingNode myNode)
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
    let getTime = trace "TODO create node wide synchronized getTime function" getLocalTime

    -- Gather Listeners (list of "on some behavior changed, perform some IO action")
    --    TODO allow IO listeners to be specified in the Moment monad and saved in the Circuit
    --    Add IO listeners for sending Msgs to other nodes.
    let responsabilities = error "TODO" :: [Responsibility myNode]

    -- Get all source behaviors for this node.
    let mySourceEs :: [EventIx myNode LocalInput]
        mySourceEs = mapMaybe
            (\case
                GateIx' (GateIxB (BehaviorIx b)) -> cast b
                GateIx' (GateIxE (EventIx    e)) -> cast e)
            (circAllGates circuit)

    -- A single change to compile all local inputs and messages from other nodes.
    inChan :: Chan (Time, [Update]) <- newChan

    -- Listen for local inputs (time is assigned here)
    _ <- forkIO . forever $ do
        input <- readChan localInChan
        time <- getTime
        writeChan inChan (time, [UpdateE e input | e <- mySourceEs])

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

mkLiveCircuit :: Circuit -> LiveCircuit
mkLiveCircuit c = fst (lcTransaction shortCircuit 0 [])
    where
        shortCircuit =  LiveCircuit
            { lcCircuit     = c
            , lcGateMaxT    = const (-1)
            , lcBehVal      = error "Imposible! failed to set initial behavior value."
            , lcEvents      = const []
            }

lcBehValTimeError :: a
lcBehValTimeError = error "Attempt to access behavior value outside of known time."

-- Transactionally update the circuit. Returns (_, changed behaviors (lcBehMaxT has increased))
lcTransaction :: LiveCircuit -> Time -> [Update] -> (LiveCircuit, [()])
lcTransaction lc t ups = (lintLiveCircuit LiveCircuit
    { lcCircuit     = c
    , lcGateMaxT    = lcGateMaxT'
    , lcBehVal      = lcBehVal'
    , lcEvents      = lcEvents'
    }, error "TODO calculate changes behaviors values, and new evetns (may be multiple occs per event! so use a list maybe)")
    where
        c = lcCircuit lc

        -- Assumption (A): since we assuem that we get complete and inorder info about each "remote" gate from a
        -- unique remote node, we can immediatelly increase lcBehMaxT and know that the value hasn't changed
        -- sine that last update we received. Likewise we can be sure that there are no earlier events that we
        -- have "missed".

        lcGateMaxT' :: forall (owner :: Node) (a :: Type) . (Typeable owner, Typeable a)
                   => GateIx owner a -> Time
        lcGateMaxT' gix = case findUpdate gix of
            -- Is updated in this transaction, so use transaction time.
            Just _ -> t
            -- Else use min of dependants. If no dependants, then no change.
            Nothing -> let
                deps = gateIxDeps c gix
                in if null deps
                    then lcGateMaxT lc gix -- No change
                    else minimum $ (\(GateIx' dep) -> lcGateMaxT' dep) <$> deps

        -- TODO/NOTE this is super inefficient
        lcBehVal' :: forall (owner :: Node) a . (Typeable owner, Typeable a)
                 => Time -> BehaviorIx owner a -> Maybe a
        lcBehVal' t' b
            | t' > lcGateMaxT' bGateIx = Nothing
            | otherwise          = case findUpdate (GateIxB b) of
                -- Is updated in this transaction, so use transaction value.
                -- TODO can we get rid of the unsafeCoerce here? We know the type is correct
                Just val -> unsafeCoerce $ Just val
                -- Else use min of dependants. If no dependants, then no change.
                Nothing -> case circBeh c b of
                    Step aInit eA -> let
                                    evtOccs = lcEvents' eA
                                    occMay = find ((t'>=) . fst) evtOccs  -- Note (>=) implies value changes *on* the event not after.
                                    in Just (maybe aInit snd occMay)    -- Is it correct to accept t < 0?
                    MapB f bA    -> f <$> lcBehVal' t' bA
                    Ap fb ib     -> let
                        -- The values should be known, we we use fromJust to fail fast.
                        f = fromJust (lcBehVal' t' fb)
                        i = fromJust (lcBehVal' t' ib)
                        in Just (f i)
                    -- Send doesnt change the value from bA. Note that this subtly implies that when the owner sends
                    -- the value, it sends it as the value of bA, not the (SendB _ bA) behavior. (***)
                    SendB _ bA   -> lcBehVal' t' bA
            where
                bGateIx = GateIxB b

        lcEvents'  :: forall (owner :: Node) a . (Typeable owner, Typeable a)
                => EventIx owner a -> [(Time, a)]
        lcEvents' e = case findUpdate (GateIxE e) of
            Just val -> (t, val) : previousOccs
            Nothing -> case circEvt c e of
                -- Nothing for source event even if it is local, because we will get this as an Update.
                Source _        -> previousOccs
                MapE f eA       -> (\(occT, occVal) -> (occT, f occVal)) <$> lcEvents' eA
                Sample f b eA   -> [(t', f bVal eVal) | (t', eVal) <- lcEvents' eA
                                                      , let bVal = fromJust (lcBehVal' t' b) ]
                -- See (***) note on SendB case above.
                SendE _ eA      -> lcEvents' eA
            where
                previousOccs = lcEvents lc e

        findUpdate :: GateIx owner a -> Maybe a
        findUpdate g = headMay (mapMaybe maybeVal ups)
            where
                gv = case g of
                    GateIxB (BehaviorIx bv) -> bv
                    GateIxE (EventIx    ev) -> ev
                maybeVal (UpdateB (BehaviorIx v) val)
                    | v == gv   = Just (unsafeCoerce val)
                    | otherwise = Nothing
                maybeVal (UpdateE (EventIx    v) val)
                    | v == gv   = Just (unsafeCoerce val)
                    | otherwise = Nothing

-- Assertiong on LiveCircuitls
lintLiveCircuit :: LiveCircuit -> LiveCircuit
lintLiveCircuit = id -- TODO