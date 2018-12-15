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
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module NFRP
    ( module NFRP
    , module TypeLevelStuff
    ) where

import Safe
import Control.Monad.State
import Unsafe.Coerce
import Data.Typeable (cast, typeRep)
import Data.IORef
import Data.Proxy
import Data.Kind
import Data.Dynamic
import Data.Maybe (mapMaybe)
import Data.List (find, sortBy)
import Data.Function (on)
import qualified Data.Graph as Graph
import qualified Data.Map as Map

import Control.Concurrent
import Control.Concurrent.Async

import Debug.Trace
import Control.Exception.Base (assert)

import TypeLevelStuff

data GateIx' = forall (os :: [Node]) (a :: Type) . (Typeable os, Typeable a) => GateIx' (GateIx os a)
data GateIx (os :: [Node]) (a :: Type) = GateIxB (BehaviorIx os a) | GateIxE (EventIx os a)

data BehaviorIx' = forall (os :: [Node]) (a :: Type) . (Typeable os, Typeable a) => BehaviorIx' (BehaviorIx os a)
newtype BehaviorIx (os :: [Node]) (a :: Type) = BehaviorIx { bixVert :: Graph.Vertex }
        deriving (Eq, Ord)
data Behavior (os :: [Node]) (a :: Type) where
    Step :: (Typeable os, Typeable a)
        => a -> EventIx os a -> Behavior os a
    MapB :: (Typeable os, Typeable a, Typeable b)
        => (a -> b) -> BehaviorIx os a -> Behavior os b
    Ap  :: (Typeable os, Typeable a, Typeable b)
        => BehaviorIx os (a -> b) -> BehaviorIx os a -> Behavior os b
    SendB :: forall (fromNode :: Node) (fromOs :: [Node]) (toOs :: [Node]) a
         .  ( IsElem fromNode fromOs
            , Typeable fromOs
            , Typeable toOs
            , Typeable fromNode
            , Typeable toOs
            , Typeable a
            , SingNode fromNode
            , AllC SingNode toOs)
         => (Proxy fromNode)
         -> (Proxy toOs)
         -> BehaviorIx fromOs a
         -> Behavior toOs a
data EventIx' = forall (o :: [Node]) (a :: Type) . (Typeable o, Typeable a) => EventIx' (EventIx o a)
newtype EventIx (os :: [Node]) (a :: Type) = EventIx { eixVert :: Graph.Vertex }
        deriving (Eq, Ord)
data Event (os :: [Node]) (a :: Type) where
    Source :: forall (node :: Node)
        .  (Proxy node)
        -> Event '[node] LocalInput
    MapE :: (Typeable os, Typeable a, Typeable b)
        => (a -> b) -> EventIx os a -> Event os b
    Sample :: (Typeable os, Typeable a, Typeable b, Typeable c)
        => (a -> b -> c) -> BehaviorIx os a -> EventIx os b -> Event os c
    SendE :: (Typeable fromNode, Typeable toNode, Typeable a)
        => (Proxy toNode)
        -> EventIx fromNode a
        -> Event toNode a


data Circuit = Circuit
    { circGraph    :: Graph.Graph
    , circGateDyn  :: Map.Map Graph.Vertex Dynamic
                    -- ^Dynamic is a Behavior or Event of some os/type (can be infered from vertex)
    , circAllGates :: [GateIx']
    }

circBeh :: forall (os :: [Node]) a . (Typeable os, Typeable a)
        => Circuit -> BehaviorIx os a -> Behavior os a
circBeh c = flip fromDyn (error "Unexpected type of behavior.") . (circGateDyn c Map.!) . bixVert

circEvt :: forall (os :: [Node]) a . (Typeable os, Typeable a)
        => Circuit -> EventIx os a -> Event os a
circEvt c = flip fromDyn (error "Unexpected type of event.") . (circGateDyn c Map.!) . eixVert

data LiveCircuit (os :: [Node]) = LiveCircuit
    { lcCircuit :: Circuit
    , lcBehChanges  :: forall (o' :: [Node]) a . (Typeable o', Typeable a)
                    => BehaviorIx o' a -> [(Time, a)]
                    -- ^ Value of a behavior at a time. Time must be <= lcBehMaxT else Nothing.
    , lcEvents  :: forall (o' :: [Node]) a . (Typeable o', Typeable a)
                    => EventIx o' a    -> [(Time, a)]
                    -- ^ Complete events up to lcGateMaxT time in reverse chronological order.
    }


lcGateMaxT :: forall myNode (o' :: [Node]) a . (Typeable o', Typeable a)
           => LiveCircuit myNode -> GateIx o' a -> Time
lcGateMaxT lc (GateIxB b) = headDef (-1) (fst <$> lcBehChanges lc b)
lcGateMaxT lc (GateIxE e) = headDef (-1) (fst <$> lcEvents lc e)

lcBehVal :: (Typeable o2, Typeable a)
         => LiveCircuit o1 -> Time -> BehaviorIx o2 a -> a
lcBehVal lc t bix
    | t > maxT  = err
    | otherwise = maybe err snd (find ((<=t) . fst) cs)
    where
        cs = lcBehChanges lc bix
        maxT = lcGateMaxT lc (GateIxB bix)
        err = error $
            "Trying to access behavior valur at time " ++ show t
            ++ " but only know till time " ++ show maxT


instance Eq BehaviorIx' where
    (BehaviorIx' (BehaviorIx v1)) == (BehaviorIx' (BehaviorIx v2)) = v1 == v2

-- Now we'd like a monad to build this circuit in
type Moment ctxF a = State (MomentState ctxF) a
data MomentState (ctxF :: Node -> Type) = MomentState
    { momentNextVert  :: Graph.Vertex
    , momentBehDyn    :: Map.Map Graph.Vertex Dynamic
    , momentEdges     :: [Graph.Edge]
    , momentAllGates  :: [GateIx']
    , momentListeners :: [Listener ctxF]
    }

data Listener (ctxF :: Node -> Type)
    = forall n os a
    . (IsElem n os, Typeable n, Typeable os, Typeable a)
    => Listener (Proxy n) (BehaviorIx os a) (ctxF n -> a -> IO ())

data UpdateList = forall os a . (Typeable os, Typeable a)
                => UpdateListB (BehaviorIx os a) [(Time, a)]
            | forall os a . (Typeable os, Typeable a)
                => UpdateListE (EventIx    os a) [(Time, a)]

data Responsibility localCtx (responsibleNode :: Node)
    = forall (os :: [Node]) a . (Typeable os, Typeable a) =>
        OnPossibleChange
            (BehaviorIx os a)
            Bool    -- ^ Is it a local listerner? As opposed to sending a msg to another node.
            (localCtx -> a -> IO ())

beh :: (Typeable os, Typeable a)
    => Behavior os a -> Moment ctxF (BehaviorIx os a)
beh b = do
    MomentState v bd es allGates ls <- get
    let behIx = BehaviorIx v
    put $ MomentState
            -- Increment vertex index.
            (v+1)
            -- Add behavior to map.
            (Map.insert v (toDyn behIx) bd)
            -- Add eges and behavior.
            (((v,) <$> behDepVerts b) ++ es)
            (GateIx' (GateIxB behIx) : allGates)
            ls
    return behIx

evt :: (Typeable os, Typeable a)
    => Event os a -> Moment ctxF (EventIx os a)
evt e = do
    MomentState v bd es allGates ls <- get
    let evtIx = EventIx v
    put $ MomentState
            -- Increment vertex index.
            (v+1)
            -- Add event to map.
            (Map.insert v (toDyn evtIx) bd)
            -- Add eges and event.
            (((v,) <$> evtDepVerts e) ++ es)
            (GateIx' (GateIxE evtIx) : allGates)
            ls
    return evtIx

(===) :: (Typeable a, Typeable b, Eq a) => a -> b -> Bool
a === b = Just a == cast b

behDepVerts :: Behavior os a -> [Graph.Vertex]
behDepVerts (Step _ e)    = [eixVert e]
behDepVerts (MapB _ b)    = [bixVert b]
behDepVerts (Ap fb ib)    = [bixVert fb, bixVert ib]
behDepVerts (SendB _ _ b) = [bixVert b]

behDeps :: (Typeable os, Typeable a) => Behavior os a -> [GateIx']
behDeps (Step _ e)    = [GateIx' (GateIxE e)]
behDeps (MapB _ b)    = [GateIx' (GateIxB b)]
behDeps (Ap fb ib)    = [GateIx' (GateIxB fb), GateIx' (GateIxB ib)]
behDeps (SendB _ _ b) = [GateIx' (GateIxB b)]

evtDepVerts :: Event os a -> [Graph.Vertex]
evtDepVerts (Source _)     = []
evtDepVerts (MapE _ e)     = [eixVert e]
evtDepVerts (Sample _ b e) = [bixVert b, eixVert e]
evtDepVerts (SendE _ e)    = [eixVert e]

evtDeps :: (Typeable os, Typeable a) => Event os a -> [GateIx']
evtDeps (Source _)     = []
evtDeps (MapE _ e)     = [GateIx' (GateIxE e)]
evtDeps (Sample _ b e) = [GateIx' (GateIxB b), GateIx' (GateIxE e)]
evtDeps (SendE _ e)    = [GateIx' (GateIxE e)]

gateIxDeps :: (Typeable os, Typeable a) => Circuit -> GateIx os a -> [GateIx']
gateIxDeps c (GateIxB bix) = behDeps $ circBeh c bix
gateIxDeps c (GateIxE eix) = evtDeps $ circEvt c eix

listenB :: (IsElem n os, Typeable os, Typeable n, Typeable a)
        => Proxy n -> BehaviorIx os a -> (ctxF n -> a -> IO ()) -> Moment ctxF ()
listenB node bix listener = modify (\ms -> ms {
        momentListeners = Listener node bix listener : momentListeners ms
    })

buildCircuit :: Moment ctxF () -> (Circuit, [Listener ctxF])
buildCircuit builder
    = ( Circuit graph behDyn allBehs
      , ls
      )
    where
        (_, MomentState nextVIx behDyn edges allBehs ls) = runState builder (MomentState 0 Map.empty [] [] [])
        graph = Graph.buildG (0, nextVIx - 1) edges


-- Lets make a simple calculator example with 3 clients and a server that we want to do that calculating.
data Node
    = ClientA
    | ClientB
    | ClientC
    | Server
    deriving (Eq, Ord, Bounded, Enum)

class SingNode (node :: Node) where singNode :: Proxy node -> Node
instance SingNode ClientA where singNode _ = ClientA
instance SingNode ClientB where singNode _ = ClientB
instance SingNode ClientC where singNode _ = ClientC
instance SingNode Server where singNode _ = Server

instance Sing ClientA where
    type SingT ClientA = Node
    sing _ = ClientA
instance Sing ClientB where
    type SingT ClientB = Node
    sing _ = ClientB
instance Sing ClientC where
    type SingT ClientC = Node
    sing _ = ClientC
instance Sing Server where
    type SingT Server = Node
    sing _ = Server

data UpdateWay
    = LocalUpdate    -- ^ updated directly by a local update event (local event)
    | RemoteUpdate   -- ^ updated directly by a remote update event (sent from a remote node)
    | DerivedUpdate  -- ^ updated by combining dependant gates
    | NoUpdate       -- ^ node's value is never updated (The value is is unknown)
    deriving (Eq, Show)

class HasUpdateWay gate where
    updateWay :: Typeable myNode => Proxy myNode -> gate -> UpdateWay
instance (Typeable o, Typeable a) => HasUpdateWay (Behavior o a) where
    updateWay myNodeP b
        | isOwned myNodeP b = case b of
            SendB {}  -> RemoteUpdate
            _         -> DerivedUpdate
        | otherwise = NoUpdate
instance (Typeable o, Typeable a) => HasUpdateWay (Event o a) where
    updateWay myNodeP b
        | isOwned myNodeP b = case b of
            SendE {}  -> RemoteUpdate
            Source {} -> LocalUpdate
            _         -> DerivedUpdate
        | otherwise = NoUpdate


isOwned :: forall o1 o2 gate a . (Typeable o1, Typeable o2) => Proxy o1 -> gate o2 a -> Bool
isOwned po1 _ = typeRep po1 == typeRep (Proxy @o2)

-- The only local input we care about is key presses.
type LocalInput = Char

type Time = Integer -- TODO Int64? nanoseconds?

actuate :: forall (myNode :: Node) (ctxF :: Node -> Type)
        .  (Typeable ctxF, Typeable myNode, SingNode myNode)
        => ctxF myNode
        -> Proxy myNode                -- What node to run.
        -> Node                        -- Clock sync node
        -> IO Time                     -- Local clock
        -> Moment ctxF ()               -- The circuit to build
        -> Chan LocalInput             -- Local inputs
        -> Map.Map Node (Chan [UpdateList], Chan [UpdateList])   -- (send, receive) Chanels to other nodes
        -> IO ()
actuate ctx
        myNodeProxy
        _clockSyncNode
        getLocalTime
        mkCircuit
        localInChan
        channels
  = do
    let myNode = singNode myNodeProxy
        (circuit, listeners) = buildCircuit mkCircuit

    -- Clock synchronize with clockSyncNode if not myNode and wait for starting time. (TODO regularly synchronize clocks).
    -- Else accept clock sync with all other nodes, then braodcast a starting time (to start the circuit).
    let getTime = trace "TODO create node wide synchronized getTime function" getLocalTime

    -- Gather Responsabilities (list of "on some behavior changed, perform some IO action")
    let myResponsabilitiesListeners :: [Responsibility (ctxF myNode) myNode]
        myResponsabilitiesListeners
            = mapMaybe (\(Listener _proxyNode bix handler)
                        -> OnPossibleChange
                                bix
                                True
                                <$> cast handler)   -- This case filters for myNode handlers
            $ listeners


        myResponsabilitiesMessage :: [Responsibility (ctxF myNode) myNode]
        myResponsabilitiesMessage
            = mapMaybe (\(GateIx' g) -> case g of
                GateIxB bix -> case circBeh circuit bix of
                    SendB fromNodeP toNodesP _bix
                        | myNode == singNode fromNodeP
                        -> Just $ OnPossibleChange bix False
                            (\ _ bixVal -> forM_ (sings toNodesP) $ \ toNode ->
                                writeChan _msg . fst $ channels Map.! toNode)
                    _ -> Nothing
                GateIxE eix -> case circEvt circuit eix of
                    SendE {} -> error "TODO support sending events" -- Just $ OnEvent bix False _doSend
                    _ -> Nothing
                )
            $ circAllGates circuit

        -- My node's responsabilities
        responsabilities :: [Responsibility (ctxF myNode) myNode]
        responsabilities = myResponsabilitiesMessage ++ myResponsabilitiesListeners

    -- Get all source behaviors for this node.
    let mySourceEs :: [EventIx '[myNode] LocalInput]
        mySourceEs = mapMaybe
            (\case
                GateIx' (GateIxB (BehaviorIx b)) -> cast b
                GateIx' (GateIxE (EventIx    e)) -> cast e)
            (circAllGates circuit)

    -- A single change to compile all local inputs and messages from other nodes.
    inChan :: Chan [UpdateList] <- newChan

    -- Listen for local inputs (time is assigned here)
    _aLocalInput <- async . forever $ do
        input <- readChan localInChan
        time <- getTime
        writeChan inChan [UpdateListE e [(time, input)] | e <- mySourceEs]

    -- Listen for messages from other nodes.
    _asRcv <- forM (Map.assocs channels) $ \(_otherNode, (_, recvChan)) -> async
        $ writeChan inChan =<< readChan recvChan

    -- Thread that just processes inChan, keeps track of the whole circuit and
    -- decides what listeners to execute (sending them to listenersChan/msgChan).
    let (circuit0, initialUpdates) = mkLiveCircuit circuit :: (LiveCircuit '[myNode], [UpdateList])
    changesChan :: Chan [UpdateList] <- newChan
    writeChan changesChan initialUpdates
    listenersChan :: Chan (IO ()) <- newChan
    outMsgChan :: Chan (IO ()) <- newChan
    liveCircuitRef <- newIORef circuit0
    _aLiveCircuit <- async . forever $ do
        -- Update state: Calculate for each behavior what is known and up to what time
        updates <- readChan inChan
        oldLiveCircuit <- readIORef liveCircuitRef
        let (newLiveCircuit, changes) = lcTransaction oldLiveCircuit updates
        writeIORef liveCircuitRef newLiveCircuit
        writeChan changesChan changes

    -- Fullfill responsibilities: Listeners + sending to other nodes
    _aResponsibilities <- async . forever $ do
        changes <- readChan changesChan
        forM_ responsabilities $ \(OnPossibleChange bix isLocalListener action) ->
            -- TODO double forM_ is inefficient
            forM_ changes $ \case
                UpdateListB bix' ((_time,latestValue):_)
                    | bix === bix'
                    -> writeChan
                        (if isLocalListener then listenersChan else outMsgChan)
                        (action ctx (unsafeCoerce latestValue))
                -- Note we don't support Event listeners (yet).
                _ -> return ()


    -- Thread that just executes listeners
    _aListeners <- async . forever . join . readChan $ listenersChan

    -- Thread that just sends messages to other nodes
    -- aSend <- async . forever . join . readChan $ outMsgChan
    _aMsg <- async . forever . join . readChan $ outMsgChan

    -- TODO some way to stop gracefully.

    -- wait aLocalInput
    -- sequence (wait <$> asRcv)
    -- wait aLiveCircuit
    -- wait aResponsibilities
    -- wait aListeners
    -- wait aSend

    return ()

mkLiveCircuit :: forall myNode . Typeable myNode
              => Circuit -> (LiveCircuit myNode, [UpdateList])
mkLiveCircuit c = (lc, initialUpdatesOwnedBeh ++ initialUpdatesDerived)
    where
        (lc, initialUpdatesDerived) = lcTransaction LiveCircuit
            { lcCircuit     = c
            , lcBehChanges  = const []
            , lcEvents      = const []
            } initialUpdatesOwnedBeh


        initialUpdatesOwnedBeh = mapMaybe
            (\case
                GateIx' (GateIxB bix)
                  | isOwned (Proxy @myNode) bix
                  -> case circBeh c bix of
                        Step bix2 _  -> Just (UpdateListB bix [(0, bix2)])
                        MapB _ _     -> Nothing
                        Ap _ _       -> Nothing
                        SendB _ _ _  -> Nothing
                _ -> Nothing
            )
            (circAllGates c)

-- Transactionally update the circuit. Returns (_, changed behaviors (lcBehMaxT has increased))
lcTransaction :: forall myNode . (Typeable myNode)
              => LiveCircuit myNode -> [UpdateList] -> (LiveCircuit myNode, [UpdateList])
lcTransaction lc ups = assert lint (lc', changes)
    where
        lc' = lintLiveCircuit LiveCircuit
                { lcCircuit     = c
                , lcBehChanges  = lcBehChanges'
                , lcEvents      = lcEvents'
                }

        changes
            = mapMaybe (\(GateIx' gix) -> let
                ta = lcGateMaxT lc  gix
                tb = lcGateMaxT lc' gix
                prune = takeWhile ((> ta) . fst)
                in if ta == tb
                    then Nothing
                    else Just $ case gix of
                        (GateIxB bix) -> UpdateListB bix (prune $ lcBehChanges lc' bix)
                        (GateIxE eix) -> UpdateListE eix (prune $ lcEvents     lc' eix))
            $ circAllGates c

        myNodeP = Proxy @myNode
        lint
            -- All updates are for Behaviors/Events are NOT derived/no-update
            =  all (not . flip elem [DerivedUpdate, NoUpdate])
                (fmap (\up -> case up of
                        UpdateListB b _ -> updateWay myNodeP (circBeh c b)
                        UpdateListE e _ -> updateWay myNodeP (circEvt c e))
                    ups)

            -- All updates are after maxT
            && all (\up -> case up of
                    UpdateListB b ul -> all (lcGateMaxT lc (GateIxB b) <) (fst <$> ul)
                    UpdateListE e ul -> all (lcGateMaxT lc (GateIxE e) <) (fst <$> ul))
                ups

        -- TODO asset that all updates are after their corresponding Event/Behavior's MaxT time.
        --      we have at most 1 UpdateList per gate

        c = lcCircuit lc

        -- Assumption (A): since we assuem that we get complete and inorder info about each "remote" gate from a
        -- unique remote node, we can immediatelly increase lcBehMaxT and know that the value hasn't changed
        -- sine the previous update we received. Likewise we can be sure that there are no earlier events that we
        -- have missed.

        -- TODO/NOTE this is super inefficient
        lcBehChanges' :: forall (os :: [Node]) a . (Typeable os, Typeable a)
                 => BehaviorIx os a -> [(Time, a)]
        lcBehChanges' bix = case updateWay myNodeP b of
            NoUpdate       -> []
            LocalUpdate    -> fromUpdatesList
            RemoteUpdate   -> fromUpdatesList
            DerivedUpdate  -> case b of
                SendB {}           -> error "SendB Behavior cannot be derived."
                Step _ eix         -> lcEvents lc' eix
                MapB f bixParent   -> fmap f <$> lcBehChanges lc' bixParent
                Ap bixF bixArg     -> apB (lcBehChanges lc' bixF) (lcBehChanges lc' bixArg)
            where
                b = circBeh c bix
                fromUpdatesList = findUpdates (GateIxB bix) ++ lcBehChanges lc bix

                apB :: [(Time, j -> k)] -> [(Time, j)] -> [(Time, k)]
                apB [] _ = []
                apB _ [] = []
                apB ((tf,f):tfs) ((ta,a):tas) = case tf `compare` ta of
                    EQ -> (tf, f a) : apB tfs tas
                    LT -> (ta, f a) : apB tfs ((ta,a):tas)
                    GT -> (tf, f a) : apB ((tf,f):tfs) tas


        lcEvents'  :: forall (os :: [Node]) a . (Typeable os, Typeable a)
                => EventIx os a -> [(Time, a)]
        lcEvents' eix = case updateWay myNodeP e of
            NoUpdate       -> []
            LocalUpdate    -> fromUpdatesList
            RemoteUpdate   -> fromUpdatesList
            DerivedUpdate  -> case e of
                -- Nothing for source event even if it is local, because we will get this as an Update.
                Source {}        -> error "Source Event cannot be derived."
                SendE {}         -> error "SendE Event cannot be derived."
                MapE f eA        -> (\(occT, occVal) -> (occT, f occVal)) <$> lcEvents' eA
                Sample f bix eA  -> [(sampleT, f bVal eVal)
                                        | (sampleT, eVal) <- lcEvents' eA
                                        , let bVal = lcBehVal lc' sampleT bix ]
            where
                e = circEvt c eix
                fromUpdatesList = findUpdates (GateIxE eix) ++ lcEvents lc eix

        findUpdates :: GateIx os a -> [(Time, a)]
        findUpdates g
            = sortBy (flip (compare `on` fst))     -- sort into reverse chronological order
            . concat
            . mapMaybe changesMay
            $ ups
            where
                gv = case g of
                    GateIxB (BehaviorIx bv) -> bv
                    GateIxE (EventIx    ev) -> ev
                changesMay (UpdateListB (BehaviorIx v) changes)
                    | v == gv   = Just (unsafeCoerce changes)
                    | otherwise = Nothing
                changesMay (UpdateListE (EventIx    v) events)
                    | v == gv   = Just (unsafeCoerce events)
                    | otherwise = Nothing

-- Asserting on LiveCircuitls
lintLiveCircuit :: LiveCircuit myNode -> LiveCircuit myNode
lintLiveCircuit = id -- TODO
