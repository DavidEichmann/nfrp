{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableSuperClasses #-}
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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module NFRP
    ( module NFRP
    , module TypeLevelStuff
    ) where

import Safe
import Control.Monad.State
import Data.Typeable (eqT, (:~:)(Refl))
import Unsafe.Coerce
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


-- Some common constraint type families
-- TODO rename to NodeC
type family NodeC (node :: Type) :: Constraint where
    NodeC node =
        ( Eq node
        , Show node
        , Ord node
        , Typeable node
        , ReifySomeNode node
        )

-- TODO rename to NodePC
type family NodePC (nodeConstr :: node) :: Constraint where
    NodePC (nodeConstr :: node) =
        ( NodeC node
        , Typeable nodeConstr
        , Sing nodeConstr
        )

type family NodePsC (ns :: [node]) :: Constraint where
    NodePsC '[] = ()
    NodePsC (x:xs) =
        ( NodePC  x
        , NodePsC xs
        )

type family GateIxC node (ns :: [node]) a :: Constraint where
    GateIxC node (ns :: [node]) a =
        ( NodePsC ns
        , NodeC node
        , Typeable ns
        , Sings ns node
        , ElemT node ns
        )

data SomeNode node = forall (nodeP :: node) . NodePC nodeP => SomeNode (Proxy nodeP)
class ReifySomeNode (node :: Type) where
    someNode :: node -> SomeNode node

data GateIx' node = forall (os :: [node]) (a :: Type) . GateIxC node os a => GateIx' (GateIx os a)
data GateIx (os :: [node]) (a :: Type) = GateIxB (BehaviorIx os a) | GateIxE (EventIx os a)

data BehaviorIx' node = forall (os :: [node]) (a :: Type) . GateIxC node os a => BehaviorIx' (BehaviorIx os a)
newtype BehaviorIx (os :: [node]) (a :: Type) = BehaviorIx { bixVert :: Graph.Vertex }
        deriving (Show, Eq, Ord)
data Behavior (os :: [node]) (a :: Type) where
    BIx :: (Typeable os) => BehaviorIx os a -> Behavior os a
    Const :: (Typeable os) => a -> Behavior os a
    Step :: (Typeable os)
        => a -> Event os a -> Behavior os a
    MapB :: (Typeable os)
        => (a -> b) -> Behavior os a -> Behavior os b
    Ap  :: (Typeable os)
        => Behavior os (a -> b) -> Behavior os a -> Behavior os b
    SendB :: forall (fromNode :: node) (fromNodes :: [node]) (toNodes :: [node]) a
         .  ( Typeable fromNode
            , GateIxC node fromNodes a
            , GateIxC node toNodes   a
            , IsElem fromNode fromNodes
            )
         => Proxy fromNode
         -> Proxy toNodes
         -> Behavior fromNodes a
         -> Behavior toNodes a
toBix :: Behavior os a -> BehaviorIx os a
toBix (BIx bix) = bix
toBix _ = error "Expected BIx constructor"

-- TODO uggg looks like we need to remove Typeable a constraint from the constructors. Is that doable? we just cant use dynamic?
instance Typeable os => Functor (Behavior os) where
    fmap   = MapB
    a <$ _ = Const a

instance Typeable os => Applicative (Behavior os) where
    pure  = Const
    (<*>) = Ap

instance Typeable os => Functor (Event os) where
    fmap   = MapE

data EventIx' node = forall (o :: [node]) (a :: Type) . (Typeable o, Typeable a) => EventIx' (EventIx o a)
newtype EventIx (os :: [node]) (a :: Type) = EventIx { eixVert :: Graph.Vertex }
        deriving (Show, Eq, Ord)
data Event (os :: [node]) (a :: Type) where
    EIx :: (Typeable os) => EventIx os a -> Event os a
    Source :: forall (sourceNode :: node) localInput
        .  (Proxy sourceNode)
        -> Event '[sourceNode] localInput
    MapE :: (Typeable os)
        => (a -> b) -> Event os a -> Event os b
    Sample :: (Typeable os, Typeable c)
        => (Time -> a -> b -> c) -> Behavior os a -> Event os b -> Event os c
    SendE :: forall (fromNode :: node) (fromNodes :: [node]) (toNodes :: [node]) a
        . ( Typeable fromNode
          , GateIxC node fromNodes a
          , GateIxC node toNodes   a
          )
        => Proxy fromNode
        -> Proxy toNodes
        -> Event fromNodes a
        -> Event toNodes a
toEix :: Event os a -> EventIx os a
toEix (EIx eix) = eix
toEix _ = error "Expected EIx constructor"
newtype SourceEvent node a where
    SourceEvent :: EventIx '[node] a -> SourceEvent node a

data Circuit node = Circuit
    { circGraph    :: Graph.Graph
    , circGateDyn  :: Map.Map Graph.Vertex Int
                    -- ^Dynamic is a Behavior or Event of some os/type (can be infered from vertex)
    , circAllGates :: [GateIx' node]
    }

circBeh :: forall (os :: [node]) a . (Typeable node, Typeable os)
        => Circuit node -> BehaviorIx os a -> Behavior os a
circBeh c = unsafeCoerce . (circGateDyn c Map.!) . bixVert

circEvt :: forall (os :: [node]) a . (Typeable node, Typeable os)
        => Circuit node -> EventIx os a -> Event os a
circEvt c = unsafeCoerce . (circGateDyn c Map.!) . eixVert

data LiveCircuit (myNode :: node) = LiveCircuit
    { lcCircuit :: Circuit node
    , lcBehChanges  :: forall (ns :: [node]) a . GateIxC node ns a
                    => BehaviorIx ns a -> [(Time, a)]
                    -- ^ Value of a behavior at a time. Time must be <= lcBehMaxT else Nothing.
    , lcEvents  :: forall (ns :: [node]) a . GateIxC node ns a
                    => EventIx ns a    -> [(Time, a)]
                    -- ^ Complete events up to lcGateMaxT time in reverse chronological order.
    }


lcGateMaxT :: forall (myNode :: node) (ns :: [node]) a
           . GateIxC node ns a
           => LiveCircuit myNode -> GateIx ns a -> Time
lcGateMaxT lc (GateIxB b) = headDef (-1) (fst <$> lcBehChanges lc b)
lcGateMaxT lc (GateIxE e) = headDef (-1) (fst <$> lcEvents lc e)

lcBehVal :: forall node (myNode :: node) (ns :: [node]) a
         .  GateIxC node ns a
         => LiveCircuit myNode -> Time -> BehaviorIx ns a -> a
lcBehVal lc t bix
    | t > maxT  = err
    | otherwise = maybe err snd (find ((<=t) . fst) cs)
    where
        cs = lcBehChanges lc bix
        maxT = lcGateMaxT lc (GateIxB bix)
        err = error $
            "Trying to access behavior valur at time " ++ show t
            ++ " but only know till time " ++ show maxT


instance Eq (BehaviorIx' node) where
    (BehaviorIx' (BehaviorIx v1)) == (BehaviorIx' (BehaviorIx v2)) = v1 == v2

-- Now we'd like a monad to build this circuit in
type Moment node ctxF a = State (MomentState ctxF) a
data MomentState (ctxF :: node -> Type) = MomentState
    { momentNextVert  :: Graph.Vertex
    , momentBehDyn    :: Map.Map Graph.Vertex Int
    , momentEdges     :: [Graph.Edge]
    , momentAllGates  :: [GateIx' node]
    , momentListeners :: [Listener ctxF]
    }

data Listener (ctxF :: node -> Type)
    = forall n os a
    . (IsElem n os, Typeable n, Typeable os)
    => Listener (Proxy n) (BehaviorIx os a) (ctxF n -> a -> IO ())

data UpdateList node = forall (os :: [node]) a . GateIxC node os a
                => UpdateListB (BehaviorIx os a) [(Time, a)]
            | forall (os :: [node]) a . GateIxC node os a
                => UpdateListE (EventIx    os a) [(Time, a)]

instance Show (UpdateList node) where
    show ul = "UpdateList (" ++ case ul of
                UpdateListB b us -> show b ++ ") Times=" ++ show (fst <$> us)
                UpdateListE e us -> show e ++ ") Times=" ++ show (fst <$> us)

data Responsibility localCtx (responsibleNode :: node)
    = forall (os :: [node]) a . (Typeable os) =>
        OnPossibleChange
            (BehaviorIx os a)
            Bool    -- ^ Is it a local listerner? As opposed to sending a msg to another node.
            (localCtx -> [(Time,a)] -> IO ())

instance Show (Responsibility localCtx responsibilityNode) where
    show (OnPossibleChange bix isLocal _) = "OnPossibleChange (" ++ show bix ++ ") " ++ show isLocal ++ " _"

beh :: forall node (os :: [node]) a (ctxF :: node -> Type)
    . GateIxC node os a
    => Behavior os a -> Moment node ctxF (Behavior os a)
beh = \b -> case b of
    BIx _
        -> return b
    Const _
        -> newBeh b
    Step a e
        -> newBeh =<< Step a <$> evt e
    MapB f b2
        -> newBeh =<< MapB f <$> beh b2
    Ap bf b2
        -> newBeh =<< Ap <$> beh bf <*> beh b2
    SendB pFrom pTos b2
        -> newBeh =<< SendB pFrom pTos <$> beh b2
    where
        -- New BIx flavour of Behavior from a non-BIx Behavior that only references other BIx flavoured behaviors.
        newBeh :: Behavior os a -> Moment node ctxF (Behavior os a)
        newBeh b = do
            MomentState v bd es allGates ls <- get
            let behIx = BehaviorIx v
            put $ MomentState
                    -- Increment vertex index.
                    (v+1)
                    -- Add behavior to map.
                    (Map.insert v (unsafeCoerce b) bd)
                    -- Add eges and behavior.
                    (((v,) <$> behDepVerts b) ++ es)
                    (GateIx' (GateIxB behIx) : allGates)
                    ls
            return (BIx behIx)

-- | Takes any Event and broadcasts it into a (EIx eix) constructor Event.
evt :: forall node (os :: [node]) a (ctxF :: node -> Type)
    . GateIxC node os a
    => Event os a -> Moment node ctxF (Event os a)
evt = \e -> case e of
    EIx _
        -> return e
    Source pNode
        -> newEvt (Source pNode)
    MapE f e2
        -> newEvt =<< MapE f <$> evt e2
    Sample f b e2
        -> newEvt =<< Sample f <$> beh b <*> evt e2
    SendE pFrom pTos e2
        -> newEvt =<< SendE pFrom pTos <$> evt e2
    where
        -- New EIx flavour of Event from a non-EIx Event that only references other EIx flavoured events.
        newEvt :: Event os a -> Moment node ctxF (Event os a)
        newEvt e = do
            MomentState v bd es allGates ls <- get
            let evtIx = EventIx v
            put $ MomentState
                    -- Increment vertex index.
                    (v+1)
                    -- Add event to map.
                    (Map.insert v (unsafeCoerce e) bd)
                    -- Add eges and event.
                    (((v,) <$> evtDepVerts e) ++ es)
                    (GateIx' (GateIxE evtIx) : allGates)
                    ls
            return (EIx evtIx)

newSourceEvent :: forall node (myNode :: node) (ctxF :: node -> Type) a
          .  (GateIxC node '[myNode] a)
          => Proxy myNode
          -> Moment node ctxF (SourceEvent myNode a, Event '[myNode] a)
newSourceEvent myNodeP = do
    e@(EIx eix) <- evt (Source myNodeP)
    return (SourceEvent eix, e)

behDepVerts :: Behavior os a -> [Graph.Vertex]
behDepVerts (BIx bix)     = [bixVert bix]
behDepVerts (Const _)     = []
behDepVerts (Step _ e)    = evtDepVerts e
behDepVerts (MapB _ b)    = behDepVerts b
behDepVerts (Ap fb ib)    = behDepVerts fb ++ behDepVerts ib
behDepVerts (SendB _ _ b) = behDepVerts b

behDeps :: forall node (os :: [node]) a
        .  GateIxC node os a
        => Behavior os a -> [GateIx' node]
behDeps (BIx bix)     = [GateIx' (GateIxB bix)]
behDeps (Const _)     = []
behDeps (Step _ e)    = evtDeps e
behDeps (MapB _ b)    = behDeps b
behDeps (Ap fb ib)    = behDeps fb ++ behDeps ib
behDeps (SendB _ _ b) = behDeps b

evtDepVerts :: Event os a -> [Graph.Vertex]
evtDepVerts (EIx eix)      = [eixVert eix]
evtDepVerts (Source _)     = []
evtDepVerts (MapE _ e)     = evtDepVerts e
evtDepVerts (Sample _ b e) = behDepVerts b ++ evtDepVerts e
evtDepVerts (SendE _ _ e)  = evtDepVerts e

evtDeps :: forall node (os :: [node]) a
        .  GateIxC node os a
        => Event os a -> [GateIx' node]
evtDeps (EIx eix)      = [GateIx' (GateIxE eix)]
evtDeps (Source _)     = []
evtDeps (MapE _ e)     = evtDeps e
evtDeps (Sample _ b e) = behDeps b ++ evtDeps e
evtDeps (SendE _ _ e)  = evtDeps e

gateIxDeps :: forall node (os :: [node]) a
           .  GateIxC node os a
           => Circuit node -> GateIx os a -> [GateIx' node]
gateIxDeps c (GateIxB bix) = behDeps $ circBeh c bix
gateIxDeps c (GateIxE eix) = evtDeps $ circEvt c eix

listenB :: forall node (n :: node) (os :: [node]) a ctxF
        .  (GateIxC node os a, IsElem n os, Typeable n)
        => Proxy n -> Behavior os a -> (ctxF n -> a -> IO ()) -> Moment node ctxF ()
listenB node b listener = do
    BIx bix <- beh b
    modify (\ms -> ms {
        momentListeners = Listener node bix listener : momentListeners ms
    })

buildCircuit :: forall node (ctxF :: node -> Type) out
             .  Moment node ctxF out -> (Circuit node, [Listener ctxF], out)
buildCircuit builder
    = ( Circuit graph behDyn allBehs
      , ls
      , out
      )
    where
        (out, MomentState nextVIx behDyn edges allBehs ls) = runState builder (MomentState 0 Map.empty [] [] [])
        graph = Graph.buildG (0, nextVIx - 1) edges

data UpdateWay
    = LocalUpdate    -- ^ updated directly by a local update event (local event)
    | RemoteUpdate   -- ^ updated directly by a remote update event (sent from a remote node)
    | DerivedUpdate  -- ^ updated by combining dependant gates
    | NoUpdate       -- ^ node's value is never updated (The value is is unknown)
    deriving (Eq, Show)

class HasUpdateWay (gate :: [node] -> Type -> Type) where
    updateWay :: forall (myNode :: node) (os :: [node]) a
              .  (NodePC myNode, GateIxC node os a)
              => Proxy myNode -> gate os a -> UpdateWay
instance HasUpdateWay Behavior where
    updateWay (myNodeP :: Proxy myNode) b
        | isOwned myNodeP b = case b of
            SendB (_ :: Proxy fromNode) _ _ -> case eqT @myNode @fromNode of
                                        Just Refl -> DerivedUpdate
                                        Nothing   -> RemoteUpdate
            _         -> DerivedUpdate
        | otherwise = NoUpdate
instance HasUpdateWay Event where
    updateWay (myNodeP :: Proxy myNode) b
        | isOwned myNodeP b = case b of
            SendE (_ :: Proxy fromNode) _ _  -> case eqT @myNode @fromNode of
                                    Just Refl -> DerivedUpdate
                                    Nothing   -> RemoteUpdate
            Source {} -> LocalUpdate
            _         -> DerivedUpdate
        | otherwise = NoUpdate


isOwned :: forall (myNode :: node) (o2 :: [node]) gate a
        . (NodePC myNode, ElemT node o2)
        => Proxy myNode -> gate o2 a -> Bool
isOwned po1 _ = elemT po1 (Proxy @o2)

type Time = Integer -- TODO Int64? nanoseconds?

data EventInjector myNode where
    EventInjector :: Proxy myNode
                  -> (forall a . SourceEvent myNode a -> a -> IO ())
                  -> EventInjector myNode

injectEvent :: EventInjector myNode -> SourceEvent myNode a -> a -> IO ()
injectEvent (EventInjector _ injector) = injector

actuate :: forall (myNode :: node) (ctxF :: node -> Type) mkCircuitOut
        .  (NodePC myNode)
        => ctxF myNode
        -> Proxy myNode                -- What node to run.
        -> node                        -- Clock sync node
        -> IO Time                     -- Local clock
        -> Moment node ctxF mkCircuitOut               -- The circuit to build
        -> Map.Map node (Chan [UpdateList node], Chan [UpdateList node])   -- (send, receive) Chanels to other nodes
        -> IO ( IO ()               -- IO action that stops the actuation
              , mkCircuitOut                   -- Result of building the circuit
              , EventInjector myNode
                                    -- ^ function to inject events
              , IO Time             -- ^ adjusted local time.
              )
actuate ctx
        myNodeProxy
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

    let myNode = sing myNodeProxy
        (circuit, listeners, mkCircuitOut) = buildCircuit mkCircuit

        putLog :: String -> IO ()
        putLog str = putStrLn $ show myNode ++ ": " ++ str

    -- Clock synchronize with clockSyncNode if not myNode and wait for starting time. (TODO regularly synchronize clocks).
    -- Else accept clock sync with all other nodes, then braodcast a starting time (to start the circuit).
    let getTime = trace "TODO create node wide synchronized getTime function" getLocalTime

    -- Gather Responsabilities (list of "on some behavior changed, perform some IO action")
    let myResponsabilitiesListeners :: [Responsibility (ctxF myNode) myNode]
        myResponsabilitiesListeners
            = mapMaybe (\case
                Listener (_ :: Proxy myNode') bix handler
                    | Just Refl <- eqT @myNode @myNode'
                    -> Just $ OnPossibleChange
                                bix
                                True
                                (\ctx' ups -> handler ctx' (snd . head $ ups))   -- This case filters for myNode handlers
                _   -> Nothing)
            $ listeners


        myResponsabilitiesMessage :: [Responsibility (ctxF myNode) myNode]
        myResponsabilitiesMessage
            = mapMaybe (\(GateIx' g) -> case g of
                GateIxB bix -> case circBeh circuit bix of
                    SendB (_ :: Proxy fromNode) toNodesP _bix
                        | Just Refl <- eqT @myNode @fromNode
                        -> Just $ OnPossibleChange bix False
                            (\ _ bixUpdates -> forM_ (filter (/= myNode) $ sings toNodesP) $ \ toNode -> let
                                sendChan = fst (channels Map.! toNode)
                                in do
                                    putLog "Sending updates"
                                    writeChan sendChan [UpdateListB bix bixUpdates]
                            )
                    _ -> Nothing
                GateIxE eix -> case circEvt circuit eix of
                    SendE {} -> error "TODO support sending events" -- Just $ OnEvent bix False _doSend
                    _ -> Nothing
                )
            $ circAllGates circuit

        -- My node's responsabilities
        responsabilities :: [Responsibility (ctxF myNode) myNode]
        responsabilities = myResponsabilitiesMessage ++ myResponsabilitiesListeners

    putLog $ show myResponsabilitiesListeners ++ " my listener responsabilities"
    putLog $ show (length $ circAllGates circuit) ++ " gates"
    putLog $ show myResponsabilitiesMessage ++ " my message responsabilities"

    -- A single change to compile all local inputs and messages from other nodes.
    inChan :: Chan [UpdateList node] <- newChan

    -- Listen for local inputs (time is assigned here)
    let injectInput :: EventInjector myNode
        injectInput = EventInjector myNodeProxy $ \ (SourceEvent eix) valA -> do
            time <- getTime
            writeChan inChan [UpdateListE eix [(time, valA)]]

    -- Listen for messages from other nodes.
    _asRcv <- forM (Map.assocs channels) $ \(_otherNode, (_, recvChan)) -> forkIO
        . readUntillStop recvChan $ \ recvVal -> do
            writeChan inChan recvVal
            putLog "received input"

    -- Thread that just processes inChan, keeps track of the whole circuit and
    -- decides what listeners to execute (sending them to listenersChan/msgChan).
    let (circuit0, initialUpdates) = mkLiveCircuit circuit :: (LiveCircuit myNode, [UpdateList node])
    changesChan :: Chan [UpdateList node] <- newChan
    writeChan changesChan initialUpdates
    _aLiveCircuit <- do
        liveCircuitRef <- newIORef circuit0
        forkIO . readUntillStop inChan $ \ updates -> do
            -- Update state: Calculate for each behavior what is known and up to what time
            oldLiveCircuit <- readIORef liveCircuitRef
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
            \ (OnPossibleChange (bix :: BehaviorIx bixO bixA) isLocalListener action) ->
                -- TODO double forM_ is inefficient... maybe index changes on BehaviorIx?
                forM_ changes $ \ case
                    UpdateListB (bix' :: BehaviorIx bixO' bixA') updates
                        -- | Just Refl <- eqT @(BehaviorIx bixO bixA) @(BehaviorIx bixO' bixA')
                        | bixVert bix == bixVert bix'
                        -> do
                            putLog $ "Found listener for bix: " ++ show bix
                            writeChan
                                (if isLocalListener then listenersChan else outMsgChan)
                                (action ctx (unsafeCoerce updates))
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

mkLiveCircuit :: forall (myNode :: node) . NodePC myNode
              => Circuit node -> (LiveCircuit myNode, [UpdateList node])
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
                        BIx _        -> error "Unexpected BIx."
                        Const val    -> Just (UpdateListB bix [(0, val)])
                        Step bix2 _  -> Just (UpdateListB bix [(0, bix2)])
                        MapB _ _     -> Nothing
                        Ap _ _       -> Nothing
                        SendB _ _ _  -> Nothing
                _ -> Nothing
            )
            (circAllGates c)

-- Transactionally update the circuit. Returns (_, changed behaviors/events (lcBehMaxT has increased))
lcTransaction :: forall node (myNode :: node)
              .   NodePC myNode
              => LiveCircuit myNode -> [UpdateList node] -> (LiveCircuit myNode, [UpdateList node])
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
        lcBehChanges' :: forall (ns :: [node]) a
                      .  GateIxC node ns a
                      => BehaviorIx ns a -> [(Time, a)]
        lcBehChanges' bix = case updateWay myNodeP b of
            NoUpdate       -> []
            LocalUpdate    -> fromUpdatesList
            RemoteUpdate   -> fromUpdatesList
            DerivedUpdate  -> case b of
                BIx _                            -> error "Unexpected BIx."
                Const _                          -> lcBehChanges lc' bix   -- No change!
                SendB _ _ (toBix -> bix')        -> lcBehChanges lc' bix'
                Step _ (toEix -> eix)            -> lcEvents lc' eix
                MapB f (toBix -> bixParent)      -> fmap f <$> lcBehChanges lc' bixParent
                Ap (toBix -> bixF) (toBix -> bixArg)  -> apB (lcBehChanges lc' bixF) (lcBehChanges lc' bixArg)
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


        lcEvents' :: forall (ns :: [node]) a
                  .  GateIxC node ns a
                  => EventIx ns a -> [(Time, a)]
        lcEvents' eix = case updateWay myNodeP e of
            NoUpdate       -> []
            LocalUpdate    -> fromUpdatesList
            RemoteUpdate   -> fromUpdatesList
            DerivedUpdate  -> case e of
                -- Nothing for source event even if it is local, because we will get this as an Update.
                Source {}                    -> error "Source Event cannot be derived."
                EIx _                        -> error "Unexpected EIx"
                SendE _ _ (toEix -> eix')         -> lcEvents lc' eix'
                MapE f (toEix -> eA)              -> (\(occT, occVal) -> (occT, f occVal)) <$> lcEvents' eA
                Sample f (toBix -> bix) (toEix -> eA)  -> [(sampleT, f sampleT bVal eVal)
                                        | (sampleT, eVal) <- lcEvents' eA
                                        , let bVal = lcBehVal lc' sampleT bix ]
            where
                e = circEvt c eix
                fromUpdatesList = findUpdates (GateIxE eix) ++ lcEvents lc eix

        findUpdates :: forall (ns :: [node]) a
                    .  GateIxC node ns a
                    => GateIx ns a -> [(Time, a)]
        findUpdates g
            = sortBy (flip (compare `on` fst))     -- sort into reverse chronological order
            . concat
            . mapMaybe changesMay
            $ ups
            where
                gv = case g of
                    GateIxB (BehaviorIx bv) -> bv
                    GateIxE (EventIx    ev) -> ev
                changesMay (UpdateListB (BehaviorIx v :: BehaviorIx vo va) vChanges)
                    -- | Just Refl <- eqT @(BehaviorIx ns a) @(BehaviorIx vo va)
                    | v == gv   = Just (unsafeCoerce vChanges)
                    | otherwise = Nothing
                changesMay (UpdateListE (EventIx    v :: EventIx    vo va) vEvents)
                    -- | Just Refl <- eqT @(EventIx ns a) @(EventIx vo va)
                    | v == gv   = Just (unsafeCoerce vEvents)
                    | otherwise = Nothing

-- Asserting on LiveCircuitls
lintLiveCircuit :: LiveCircuit myNode -> LiveCircuit myNode
lintLiveCircuit = id -- TODO



-- Combinators
-- accumE :: a -> Event os (a -> a) -> Event os a
-- accumE a0 accE =

