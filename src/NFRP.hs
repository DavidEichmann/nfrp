{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecursiveDo #-}
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
    (
      MomentTypes
    , MomentNode
    , MomentCtx

    -- Framework
    , SourceEvent
    , EventInjector
    , newSourceEvent
    , injectEvent
    , actuate

    -- Primitives
    , Behavior ()
    , delay, constB, step, sendB, sendBAll
    , Event ()
    , sample, sendE, sendEAll
    , beh
    , evt
    , withDelay
    , listenB
    -- , accumB
    -- , accumE

    , module TypeLevelStuff
    , UpdateList
    , Moment
    , NodeC
    -- , NodePC
    -- , NodePsC
    -- , GateIxC

    -- , SomeNode (..)
    -- , ReifySomeNode (..)

    , Time

    ) where

import Safe
import Control.Monad.State
import Unsafe.Coerce
import Data.IORef
import Data.Kind
import Data.Dynamic
import Data.Maybe (mapMaybe)
import qualified Data.List as List
import Data.List (find, sortBy)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Function (on)
import qualified Data.Graph as Graph
import qualified Data.Map as Map

import Control.Concurrent
import Control.Concurrent.Async

import Control.Exception.Base (assert)

import TypeLevelStuff

import Debug.Trace

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

heartbeatFeq :: Int
heartbeatFeq = 1 -- per second

-- Some common constraint type families
type family NodeC node :: Constraint where
    NodeC node =
        ( Eq node
        , Show node
        , Ord node
        , Typeable node
        -- , ReifySomeNode node
        )

data BehTime
    = Exactly   { btTime :: Time }
    | JustAfter { btTime :: Time }
    | Inf
    deriving (Show, Eq)

minTimeBehTime :: Time -> BehTime -> Time
minTimeBehTime t (Exactly bt)   = min bt t
-- TODO this is a bit inacurate. We may be off by an infinitesimal amount of time :-(
minTimeBehTime t (JustAfter bt) = min bt t
minTimeBehTime t Inf            = t

delayBehTime :: BehTime -> BehTime
delayBehTime (Exactly t)   = JustAfter t
delayBehTime (JustAfter t) = JustAfter t
delayBehTime Inf           = Inf

instance Ord BehTime where
    compare Inf Inf = EQ
    compare Inf _ = GT
    compare _ Inf = LT
    compare a b = case btTime a `compare` btTime b of
        LT -> LT
        EQ -> case (a, b) of
            (Exactly   _, Exactly   _) -> EQ
            (JustAfter _, JustAfter _) -> EQ
            (Exactly   _, JustAfter _) -> LT
            (JustAfter _, Exactly   _) -> GT
            (Inf, _) -> error "Impossible"
            (_, Inf) -> error "Impossible"
        GT -> GT

data Owners node
    = All
    | Some [node]
    deriving (Show)

elemOwners :: Eq node => node -> Owners node -> Bool
elemOwners _ All       = True
elemOwners x (Some xs) = x `elem` xs

union :: Eq node => Owners node -> Owners node -> Owners node
union All _ = All
union _ All = All
union (Some a) (Some b) = Some (a `List.union` b)

intersect :: Eq node => Owners node -> Owners node -> Owners node
intersect All All = All
intersect All some = some
intersect some All = some
intersect (Some a) (Some b) = Some (List.intersect a b)

data GateIx' = forall (a :: Type) . GateIx' (GateIx a)
data GateIx (a :: Type) = GateIxB (BehaviorIx a) | GateIxE (EventIx a)

data Gate' node = forall (a :: Type) . Gate' (Gate node a)
data Gate node (a :: Type) = GateB (Behavior node a) | GateE (Event node a)

data BehaviorIx' = forall (a :: Type) . BehaviorIx' (BehaviorIx a)
newtype BehaviorIx (a :: Type) = BehaviorIx { bixVert :: Graph.Vertex }
        deriving (Show, Eq, Ord)
data Behavior node a where
    BIx   :: (Owners node) -> BehaviorIx a -> Behavior node a
    Delay :: (Owners node) -> a -> Behavior node a -> Behavior node a
    Const :: (Owners node) -> a -> Behavior node a
    Step  :: (Owners node) -> a -> Event node a -> Behavior node a
    MapB  :: (Owners node) -> (a -> b) -> Behavior node a -> Behavior node b
    Ap    :: (Owners node) -> Behavior node (a -> b) -> Behavior node a -> Behavior node b
    SendB :: -- forall node (fromNode :: node) (fromNodes :: [node]) (toNodes :: [node]) a .
            ( NodeC node )
         => node
         -> Owners node
         -> Behavior node a
         -> Behavior node a

toBix :: Behavior node a -> BehaviorIx a
toBix (BIx _ bix) = bix
toBix _ = error "Expected BIx constructor"

delay :: a -> Behavior node a -> Behavior node a
delay a b = Delay (owners b) a b

constB :: a -> Behavior node a
constB = Const All

step :: a -> Event node a -> Behavior node a
step a e = Step (owners e) a e

send' :: (Show node, Eq node, HasOwners gate) =>
           (node -> Owners node -> gate node a -> p)
           -> node -> Owners node -> gate node a -> p
send' sendG from tos g
    | from `elemOwners` owners g = sendG from (tos `union` (Some [from])) g
    | otherwise = error $ "Trying to send a behavior from `" ++ show from
                        ++ "` not in owners: " ++ show (owners g)
sendB :: (Show node, Ord node, Typeable node) =>
           node -> [node] -> Behavior node a -> Behavior node a
sendB    from tos = send' SendB from (Some tos)

sendBAll :: (Show node, Ord node, Typeable node) =>
              node -> Behavior node a -> Behavior node a
sendBAll from     = send' SendB from All

instance Functor (Behavior node) where
    fmap f b = MapB (owners b) f b
    a <$ b   = Const (owners b) a

instance Eq node => Applicative (Behavior node) where
    pure      = Const All
    ba <*> bb = Ap (intersect (owners ba) (owners bb)) ba bb

instance Functor (Event node) where
    fmap f b = MapE (owners b) f b

data EventIx' = forall a . EventIx' (EventIx a)
newtype EventIx (a :: Type) = EventIx { eixVert :: Graph.Vertex }
        deriving (Show, Eq, Ord)
data Event node a where
    EIx    :: Owners node -> EventIx a -> Event node a
    Source :: node -> Event node localInput
    MapE   :: Owners node -> (a -> b) -> Event node a -> Event node b
    Sample :: Owners node -> (Time -> a -> b -> c) -> Behavior node a -> Event node b -> Event node c
    SendE  :: node   -- fromNode
          -> Owners node -- toNodes
          -> Event node a
          -> Event node a

toEix :: Event os a -> EventIx a
toEix (EIx _ eix) = eix
toEix _ = error "Expected EIx constructor"

sample :: Eq node =>
            (Time -> a -> b -> c)
            -> Behavior node a -> Event node b -> Event node c
sample f b e = Sample (owners e `intersect` owners b) f b e
-- sendE' :: Eq node =>
--             node -> Owners node -> Event node a -> Event node a
-- sendE' from tos e
--     | from `elemOwners` owners e = SendE from tos e
--     | otherwise = error $ "Trying to send an event from non-owner"

sendE :: (Show node, Ord node, Typeable node)
      => node -> [node] -> Event node a -> Event node a
sendE from tos = send' SendE from (Some tos)

sendEAll :: (Show node, Ord node, Typeable node)
         => node -> Event node a -> Event node a
sendEAll from  = send' SendE from All

data SourceEvent node a where
    SourceEvent :: node -> EventIx a -> SourceEvent node a

data Circuit node = Circuit
    { circGraph    :: Graph.Graph
    , circGraphT   :: Graph.Graph  -- ^ transposed
    , circGates    :: Map.Map Graph.Vertex (Gate' node)
    , circGateIxs  :: Map.Map Graph.Vertex GateIx'
    }

class CircParents a where
    parents :: Circuit node -> a -> [GateIx']
instance CircParents Graph.Vertex where
    parents c
        = fmap (circGateIxs c Map.!)
        . Graph.reachable (circGraphT c)
instance CircParents (BehaviorIx a) where
    parents c = parents c . bixVert
instance CircParents (EventIx a) where
    parents c = parents c . eixVert

circBeh :: Circuit node -> BehaviorIx a -> Behavior node a
circBeh c ix = case circGates c Map.! bixVert ix of
                Gate' (GateB b) -> unsafeCoerce b
                _ -> error "Expected GateB but got GateE"

circEvt :: Circuit node -> EventIx a -> Event node a
circEvt c ix = unsafeCoerce $ case circGates c Map.! eixVert ix of
                Gate' (GateE e) -> unsafeCoerce e
                _ -> error "Expected GateE but got GateB"

data GateRep time a = GateRep
    { grepMaxT :: time              -- ^ grepChanges is commited up to this time.

    -- TODO it seems better to specify a start time. At the moment this is implicitelly 0 in the live circuit, or "the current maxT" when dealing with updates. We leave it up to the programmer to use (<>) correctly i.e. `updates <> currentRep` makes sense.
    -- , grepMinT :: time              -- ^ grepChanges is commited starting at this time.
    , grepChanges :: [(time, a)]    -- ^ Value changes in reverse chronolgical order. All times are <= grepMaxT.
    } deriving Show

-- | `dropUntilTime 3 [(4,_), (3,_), (2,_), (1,_)]
--                 == [       (3,_), (2,_), (1,_)]
dropUntilTime :: Ord t => t -> [(t, a)] -> [(t, a)]
dropUntilTime t = dropWhile ((> t) . fst)

instance Ord time => Semigroup (GateRep time a) where
    GateRep maxTNew newChanges <> GateRep maxTOld oldChanges
        | not (last (maxTNew : (fst <$> newChanges)) > maxTOld)
        = error "(<>) on GateRep is not commutative. The LHS must span a time period strictly after the RHS"
        | otherwise = GateRep maxTNew (newChanges ++ oldChanges)

data LiveCircuit node = LiveCircuit
    { lcCircuit :: Circuit node

    -- These are Nothing if no data is available.
    -- If Just, knowlage is complete from time=0. I.e. minT=0.
    , lcBehs :: forall a . BehaviorIx a -> Maybe (GateRep BehTime a)
    , lcEvts :: forall a . EventIx    a -> Maybe (GateRep Time    a)

    , lcNode :: node
             -- ^ What node the circuit is running on.
    }

lcBehChanges  :: LiveCircuit node -> BehaviorIx a -> [(BehTime, a)]
lcBehChanges circuit bix = maybe [] grepChanges (lcBehs circuit bix)

lcEvents      :: LiveCircuit node -> EventIx a -> [(Time, a)]
lcEvents     circuit eix = maybe [] grepChanges (lcEvts circuit eix)

lcGateMaxT :: NodeC node => LiveCircuit node -> GateIx a -> Maybe BehTime
lcGateMaxT lc (GateIxB b) = lcBehMaxT lc b
lcGateMaxT lc (GateIxE e) = Exactly <$> lcEvtMaxT lc e

lcBehMaxT :: NodeC node => LiveCircuit node -> BehaviorIx a -> Maybe BehTime
lcBehMaxT lc bix = grepMaxT <$> lcBehs lc bix

lcEvtMaxT :: NodeC node => LiveCircuit node -> EventIx a -> Maybe Time
lcEvtMaxT lc eix = grepMaxT <$> lcEvts lc eix

lcBehVal :: NodeC node => LiveCircuit node -> BehTime -> BehaviorIx a -> a
lcBehVal lc t bix = case lcBehs lc bix of
    Nothing -> error $ "Trying to access behavior value at time " ++ show t
                    ++ " but no values are known for the behavior"
    Just (GateRep maxT cs) -> if t > maxT
        then error $ "Trying to access behavior value at time " ++ show t
                    ++ " but MaxT=" ++ show maxT
        else maybe
                (error $
                    "Trying to access behavior value at time " ++ show t
                    ++ " but only know for time range: " ++ show (maxT, fst <$> cs))
                snd
                (find ((<=t) . fst) cs)

instance Eq BehaviorIx' where
    (BehaviorIx' (BehaviorIx v1)) == (BehaviorIx' (BehaviorIx v2)) = v1 == v2

data MomentTypes
    node
    ctx

type family MomentNode mts where
    MomentNode (MomentTypes node ctx) = node
type family MomentCtx mts where
    MomentCtx (MomentTypes node ctx) = ctx

-- Now we'd like a monad to build this circuit in
type Moment mt a = State (MomentState mt) a
    -- deriving (Functor, Applicative, Monad)
data MomentState momentTypes = MomentState
    { momentNextVert  :: Graph.Vertex
    -- ^ The next available gate ID.
    , momentGates     :: Map.Map Graph.Vertex (Gate' (MomentNode momentTypes))
    , momentGateIxs   :: Map.Map Graph.Vertex GateIx'
    , momentEdges     :: [Graph.Edge]
    , momentListeners :: [Listener momentTypes]
    }

data Listener mt
    = forall a
    . Listener (MomentNode mt) (BehaviorIx a) (MomentCtx mt -> a -> BehTime -> IO ())

data UpdateList
    = forall a . UpdateListB (BehaviorIx a) BehTime [(BehTime, a)]
    | forall a . UpdateListE (EventIx    a) Time    [(Time, a)]

instance Show UpdateList where
    show ul = "UpdateList (" ++ case ul of
                UpdateListB b maxT us -> show b ++ ") Times=" ++ show (maxT, fst <$> us)
                UpdateListE e maxT us -> show e ++ ") Times=" ++ show (maxT, fst <$> us)

data Responsibility node ctx
    -- | When maxT increases for a behavior do some IO.
    = forall a . OnPossibleChange
            node    -- ^ Which node's responsibility is this.
            (BehaviorIx a)
            Bool    -- ^ Is it a local listerner? As opposed to sending a msg to another node.
            (ctx -> BehTime -> [(BehTime, a)] -> IO ())
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

-- Use this when a behavior is going to be used in multiple places. The value will hence only be calculated once.
beh :: forall mt node a . (node ~ MomentNode mt, NodeC (MomentNode mt))
    => Behavior node a -> Moment mt (Behavior node a)
beh = \b -> case b of
    -- This makes sure convert all inline Behaviors/Events to BIx/EIx.
    BIx _ _
        -> return b
    Delay os a0 b2
        -> newBeh =<< Delay os a0 <$> beh b2
    Const _ _
        -> newBeh b
    Step os a e
        -> newBeh =<< Step os a <$> evt e
    MapB os f b2
        -> newBeh =<< MapB os f <$> beh b2
    Ap os bf b2
        -> newBeh =<< Ap os <$> beh bf <*> beh b2
    SendB pFrom pTos b2
        -> newBeh =<< SendB pFrom pTos <$> beh b2
    where
        -- New BIx flavour of Behavior from a non-BIx Behavior that only references other BIx flavoured behaviors.
        newBeh :: Behavior node a -> Moment mt (Behavior node a)
        newBeh b = do
            MomentState v gates gateIxs edges listeners <- get
            let behIx = BehaviorIx v
            put $ MomentState
                    -- Increment vertex index.
                    (v+1)
                    -- Add behavior(Ix) to map.
                    (Map.insert v (Gate'   (GateB b))       gates  )
                    (Map.insert v (GateIx' (GateIxB behIx)) gateIxs)
                    -- Add eges and behavior.
                    (((v,) <$> behDepVerts b) ++ edges)
                    listeners
            return (BIx (owners b) behIx)

-- | Takes any Event node and broadcasts it into a (EIx eix) constructor Event.
evt :: forall node a mt . (node ~ MomentNode mt, NodeC (MomentNode mt))
    => Event node a -> Moment mt (Event node a)
evt = \e -> case e of
    EIx _ _
        -> return e
    Source pNode
        -> newEvt (Source pNode)
    MapE os f e2
        -> newEvt =<< MapE os f <$> evt e2
    Sample os f b e2
        -> newEvt =<< Sample os f <$> beh b <*> evt e2
    SendE pFrom pTos e2
        -> newEvt =<< SendE pFrom pTos <$> evt e2
    where
        -- New EIx flavour of Event from a non-EIx Event that only references other EIx flavoured events.
        newEvt :: Event node a -> Moment mt (Event node a)
        newEvt e = do
            MomentState v gates gateIxs es ls <- get
            let evtIx = EventIx v
            put $ MomentState
                    -- Increment vertex index.
                    (v+1)
                    -- Add event to map.
                    (Map.insert v (Gate'   (GateE e))       gates  )
                    (Map.insert v (GateIx' (GateIxE evtIx)) gateIxs)
                    -- Add eges and event.
                    (((v,) <$> evtDepVerts e) ++ es)
                    ls
            return (EIx (owners e) evtIx)

newSourceEvent :: (node ~ MomentNode mt, NodeC (MomentNode mt))
    => node
    -> Moment mt (SourceEvent node a, Event node a)
newSourceEvent myNode = do
    e@(EIx _os eix) <- evt (Source myNode)
    return (SourceEvent myNode eix, e)

behDepVerts :: Behavior node a -> [Graph.Vertex]
behDepVerts (BIx _ bix)     = [bixVert bix]
behDepVerts (Const _ _)     = []
behDepVerts (Delay _ _ b)   = behDepVerts b
behDepVerts (Step _ _ e)    = evtDepVerts e
behDepVerts (MapB _ _ b)    = behDepVerts b
behDepVerts (Ap _ fb ib)    = behDepVerts fb ++ behDepVerts ib
behDepVerts (SendB _ _ b)   = behDepVerts b

-- behDeps :: NodeC node
--         => Behavior node a -> [GateIx']
-- behDeps (BIx _ bix)     = [GateIx' (GateIxB bix)]
-- behDeps (Const _ _)     = []
-- behDeps (Delay _ _ b)   = behDeps b
-- behDeps (Step _ _ e)    = evtDeps e
-- behDeps (MapB _ _ b)    = behDeps b
-- behDeps (Ap _ fb ib)    = behDeps fb ++ behDeps ib
-- behDeps (SendB _ _ b)   = behDeps b

evtDepVerts :: Event node a -> [Graph.Vertex]
evtDepVerts (EIx _ eix)      = [eixVert eix]
evtDepVerts (Source _)       = []
evtDepVerts (MapE _ _ e)     = evtDepVerts e
evtDepVerts (Sample _ _ b e) = behDepVerts b ++ evtDepVerts e
evtDepVerts (SendE _ _ e)    = evtDepVerts e

-- evtDeps :: NodeC node
--         => Event node a -> [GateIx']
-- evtDeps (EIx _ eix)      = [GateIx' (GateIxE eix)]
-- evtDeps (Source _)       = []
-- evtDeps (MapE _ _ e)     = evtDeps e
-- evtDeps (Sample _ _ b e) = behDeps b ++ evtDeps e
-- evtDeps (SendE _ _ e)    = evtDeps e

-- gateIxDeps :: NodeC node
--            => Circuit node -> GateIx a -> [GateIx']
-- gateIxDeps c (GateIxB bix) = behDeps $ circBeh c bix
-- gateIxDeps c (GateIxE eix) = evtDeps $ circEvt c eix

listenB :: (NodeC (MomentNode mt))
        => (MomentNode mt) -> Behavior (MomentNode mt) a -> (MomentCtx mt -> a -> BehTime -> IO ()) -> Moment mt ()
listenB node b listener
    | node `elemOwners` owners b = do
        BIx _ bix <- beh b
        modify (\ms -> ms {
            momentListeners = Listener node bix listener : momentListeners ms
        })
    | otherwise = error "Trying to listen to non-owned behavior"

buildCircuit :: Moment mt out -> (Circuit (MomentNode mt), [Listener mt], out)
buildCircuit builder
    = ( Circuit graph (Graph.transposeG graph) gates gateIxs
      , ls
      , out
      )
    where
        (out, MomentState nextVIx gates gateIxs edges ls) = runState builder (MomentState 0 Map.empty Map.empty [] [])
        graph = Graph.buildG (0, nextVIx - 1) edges

data UpdateWay
    = LocalUpdate    -- ^ updated directly by a local update event (local event)
    | RemoteUpdate   -- ^ updated directly by a remote update event (sent from a remote node)
    | DerivedUpdate  -- ^ updated by combining dependant gates
    | NoUpdate       -- ^ node's value is never updated (The value is is unknown)
    deriving (Eq, Show)

class HasUpdateWay (gate :: Type -> Type -> Type) where
    updateWay :: NodeC node
              => node -> gate node a -> UpdateWay

instance HasUpdateWay Behavior where
    updateWay myNode b
        | b `isObservableTo` myNode = case b of
            SendB fromNode _ _ -> if myNode == fromNode
                                    then DerivedUpdate
                                    else RemoteUpdate
            _         -> DerivedUpdate
        | otherwise = NoUpdate

instance HasUpdateWay Event where
    updateWay myNode b
        | b `isObservableTo` myNode = case b of
            SendE fromNode _ _  -> if myNode == fromNode
                                    then DerivedUpdate
                                    else RemoteUpdate
            Source {} -> LocalUpdate
            _         -> DerivedUpdate
        | otherwise = NoUpdate

class IsObservableTo (gate :: Type -> Type -> Type) where
    isObservableTo :: Eq node => gate node a -> node -> Bool
instance HasOwners gate => IsObservableTo gate where
    isObservableTo g n = case owners g of
        All -> True
        Some ns -> n `elem` ns

class HasOwners (gate :: Type -> Type -> Type) where
    owners :: gate node a -> Owners node
instance HasOwners Behavior where
    owners b = case b of
        BIx os _         -> os
        Delay os _ _     -> os
        Const os _       -> os
        MapB os _ _      -> os
        Step os _ _      -> os
        Ap os _ _        -> os
        SendB _ os _     -> os
instance HasOwners Event where
    owners e = case e of
        EIx os _         -> os
        Source o         -> Some [o]
        MapE os _ _      -> os
        Sample os _ _ _  -> os
        SendE _ os _     -> os


type Time = Integer -- TODO Int64? nanoseconds?

data EventInjector node where
    EventInjector :: node
                  -> (forall a . SourceEvent node a -> a -> IO ())
                  -> EventInjector node

injectEvent :: (Eq node, Show node) => EventInjector node -> SourceEvent node a -> a -> IO ()
injectEvent (EventInjector nA injector) se@(SourceEvent nB _)
    | nA /= nB   = error $ "Attempting to use event injector for node \""
                        ++ show nA ++ "\" on source event for node \""
                        ++ show nB ++ "\""
    | otherwise  = injector se

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

        putLog :: String -> IO ()
        putLog str = putStrLn $ show myNode ++ ": " ++ str

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
                                (\ctx' maxT ups -> let
                                    (_updateTime, val) = head ups
                                    in handler ctx' val maxT)
                _   -> Nothing)
            $ listeners

        myResponsabilitiesMessage :: [Responsibility node ctx]
        myResponsabilitiesMessage
            = mapMaybe (\(GateIx' g) -> case g of
                GateIxB bix -> case circBeh circuit bix of
                    SendB fromNode toNodes _bix
                        | fromNode == myNode
                        -> Just $ OnPossibleChange myNode bix False
                            (\ _ maxT bixUpdates -> let
                                toNodes' = filter (/= myNode) $ case toNodes of
                                    All     -> Map.keys channels
                                    Some ns -> ns
                                in forM_ toNodes' $ \ toNode -> let
                                        sendChan = fst (channels Map.! toNode)
                                        in do
                                            putLog "Sending updates"
                                            writeChan sendChan [UpdateListB bix maxT bixUpdates]
                            )
                    _ -> Nothing
                GateIxE eix -> case circEvt circuit eix of
                    SendE {} -> error "TODO support sending events" -- Just $ OnEvent bix False _doSend
                    _ -> Nothing
                )
            $ Map.elems (circGateIxs circuit)

        allSourceEvts :: [EventIx']
        allSourceEvts
            -- Find all Send gates.
            = mapMaybe (\gateIx'@(GateIx' g) -> case g of
                GateIxB bix -> Nothing
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
            putLog "received input"

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
    -- decides what listeners to execute (sending them to listenersChan/msgChan).
    let (circuit0, initialUpdates) = mkLiveCircuit myNode circuit :: (LiveCircuit node, [UpdateList])
    changesChan :: Chan [UpdateList] <- newChan
    writeChan changesChan initialUpdates
    _aLiveCircuit <- do
        liveCircuitRef <- newIORef circuit0
        forkIO . readUntillStop inChan $ \ inChanData -> do
            -- Update state: Calculate for each behavior what is known and up to what time
            oldLiveCircuit <- readIORef liveCircuitRef
            updates <- case inChanData of
                InChan_RemoteUpdate ups -> return ups
                InChan_LocalUpdate eix valA -> do
                    time <- getTime
                    return [UpdateListE eix time [(time, valA)]]
                InChan_Heartbeat -> do
                    time <- getTime
                    return $ map
                        (\ (EventIx' eix) -> UpdateListE eix time [])
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
                    UpdateListB bix' maxT updates
                        -- | Just Refl <- eqT @(BehaviorIx bixO bixA) @(BehaviorIx bixO' bixA')
                        | bixVert bix == bixVert bix'
                        -> do
                            putLog $ "Found listener for bix: " ++ show bix
                            writeChan
                                (if isLocalListener then listenersChan else outMsgChan)
                                (action ctx maxT (unsafeCoerce updates))
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

mkLiveCircuit :: NodeC node
              => node -> Circuit node -> (LiveCircuit node, [UpdateList])
mkLiveCircuit myNode c = (lc, initialUpdatesOwnedBeh ++ initialUpdatesDerived)
    where
        (lc, initialUpdatesDerived) = lcTransaction LiveCircuit
            { lcCircuit = c
            , lcBehs = const Nothing
            , lcEvts = const Nothing
            , lcNode = myNode
            } initialUpdatesOwnedBeh

        initialUpdatesOwnedBeh = mapMaybe
            (\case
                GateIx' (GateIxB bix)
                  | circBeh c bix `isObservableTo` myNode
                  -> case circBeh c bix of
                        BIx _ _        -> error "Unexpected BIx."
                        Const _ val    -> Just (UpdateListB bix Inf [(Inf, val),(Exactly 0, val)])
                        Delay _ _ _    -> Nothing
                        Step _ val0 _  -> Just (UpdateListB bix (Exactly 0) [(Exactly 0, val0)])
                        MapB _ _ _     -> Nothing
                        Ap _ _ _       -> Nothing
                        SendB _ _ _    -> Nothing
                _ -> Nothing
            )
            (Map.elems (circGateIxs c))

-- Transactionally update the circuit. Returns (_, changed behaviors/events (lcBehMaxT has increased))
lcTransaction :: forall node
              .  NodeC node
              => LiveCircuit node -> [UpdateList] -> (LiveCircuit node, [UpdateList])
lcTransaction lc ups = lint (lc', changes)
    where
        myNode = lcNode lc
        lc' = lintLiveCircuit LiveCircuit
                { lcNode        = myNode
                , lcCircuit     = c
                , lcBehs        = lcBehs'
                , lcEvts        = lcEvts'
                }

        changes :: [UpdateList]
        changes
            = mapMaybe (\(GateIx' gix) -> let
                go :: Ord t
                    => gix
                    -> (LiveCircuit node -> Maybe (GateRep t a))
                    -> (gix -> t -> [(t, a)] -> UpdateList)
                    -> Maybe UpdateList
                go ix lcGate mkUpdateList = case (lcGate lc, lcGate lc') of
                    (Nothing, Nothing)
                        -> Nothing
                    (Nothing, Just (GateRep maxT' updates'))
                        -> Just $ mkUpdateList ix maxT' updates'
                    ( Just (GateRep maxT  _)
                     ,Just (GateRep maxT' updates') )
                        -> let newUpdates = takeWhile ((> maxT) . fst) updates'
                            in if null newUpdates
                                then Nothing
                                else Just $ mkUpdateList ix maxT' newUpdates
                    (Just _, Nothing) -> error "Impossible! Somehow we lost all info about a gate."
                in
                    case gix of
                        (GateIxB bix) -> go bix (flip lcBehs bix)    UpdateListB
                        (GateIxE eix) -> go eix (flip lcEvts eix) UpdateListE
                )
            $ Map.elems (circGateIxs c)

        lintBehRep :: Maybe (GateRep BehTime a) -> Maybe (GateRep BehTime a)
        lintBehRep  Nothing = Nothing
        lintBehRep (Just br@(GateRep _maxT cs)) = assert (not (null cs)) (Just br)

        lint
            -- Not quite true: initial values of step behaviors means you get an initial update
            -- for that behavior, yet the update way is Derived.
            -- -- All input updates are for Behaviors/Events NOT derived/no-update
            -- = assert (all (\ updateWay' -> updateWay' `notElem` [DerivedUpdate, NoUpdate])
            --     (fmap (\up -> case up of
            --             UpdateListB b _ -> updateWay myNode (circBeh c b)
            --             UpdateListE e _ -> updateWay myNode (circEvt c e))
            --         ups))

            -- All changes are after old maxT
            = assert (all (\up -> case up of
                    UpdateListB b maxT ul -> case lcBehMaxT lc b of
                        Nothing -> True
                        Just maxTOld -> all (maxTOld <) (maxT : (fst <$> ul))
                    UpdateListE e maxT ul -> case lcEvtMaxT lc e of
                        Nothing -> True
                        Just maxTOld -> all (maxTOld <) (maxT : (fst <$> ul)))
                changes)

            -- All changes are before or equal to new maxT
            . assert (all (\up -> case up of
                    UpdateListB b maxTNew ul -> case lcBehMaxT lc' b of
                        Nothing -> True
                        Just maxTOld -> all (maxTOld >=) (maxTNew : (fst <$> ul))
                    UpdateListE e maxTNew ul -> case lcEvtMaxT lc' e of
                        Nothing -> True
                        Just maxTOld -> all (maxTOld >=) (maxTNew : (fst <$> ul)))
                changes)

        -- TODO asset that all updates are after their corresponding Event/Behavior's MaxT time.
        --      we have at most 1 UpdateList per gate

        c = lcCircuit lc

        -- Assumption (A): since we assuem that we get complete and inorder info about each "remote" gate from a
        -- unique remote node, we can immediatelly increase lcBehMaxT and know that the value hasn't changed
        -- sine the previous update we received. Likewise we can be sure that there are no earlier events that we
        -- have missed.

        -- TODO/NOTE this is super inefficient
        lcBehs' :: BehaviorIx a -> Maybe (GateRep BehTime a)
        lcBehs' bix = lintBehRep $ case updateWay myNode b of
            NoUpdate       -> Nothing
            LocalUpdate    -> fromUpdatesList
            RemoteUpdate   -> fromUpdatesList
            DerivedUpdate  -> case b of
                BIx _ _                             -> error "Unexpected BIx."
                Const _ _                           -> lcBehs lc' bix   -- No change!
                Delay _ a0 (toBix -> bix')          -> delayBehRep a0 <$> (lcBehs lc' bix')
                SendB _ _ (toBix -> bix')           -> lcBehs lc' bix'
                Step _ a0 (toEix -> eix)
                    -> case lcEvts lc' eix of
                        Nothing -> Nothing
                        Just (GateRep maxTE es)
                            -> Just $ GateRep
                                (Exactly maxTE)
                                (((\ (t, val) -> (Exactly t, val)) <$> es) ++ [(Exactly 0, a0)])
                MapB _ f (toBix -> bixParent)
                    -> case lcBehs lc' bixParent of
                        Nothing -> Nothing
                        Just (GateRep maxT cs) -> Just $ GateRep maxT (fmap f <$> cs)
                Ap _ (toBix -> bixF) (toBix -> bixArg)
                    -> do
                        GateRep maxTF   fUpdates   <- lcBehs lc' bixF
                        GateRep maxTArg argUpdates <- lcBehs lc' bixArg
                        let maxT' = min maxTF maxTArg
                            updates' = apB' True (dropUntilTime maxT' fUpdates)
                                            True (dropUntilTime maxT' argUpdates)
                        return $ GateRep maxT' updates'
            where
                b = circBeh c bix
                fromUpdatesList = findBehUpdates bix <> lcBehs lc bix

                delayBehRep :: a -> GateRep BehTime a -> GateRep BehTime a
                delayBehRep a0 (GateRep maxT updates) = GateRep (delayBehTime maxT) (delayBehChanges a0 updates)

                -- Must not have 2 JustAfter t changes in a row (with the same t).
                delayBehChanges :: a -> [(BehTime, a)] -> [(BehTime, a)]
                delayBehChanges a0 []
                    = [(Exactly 0, a0)]
                delayBehChanges a0 (c0@(Inf, _) : cs)
                    = c0 : delayBehChanges a0 cs
                delayBehChanges a0 ((Exactly t, a) : cs)
                    = (JustAfter t, a) : delayBehChanges a0 cs
                -- Because it's impossible to sample the JustAfter t value for a JustAfter t  befor it,
                -- we remove it (note it can also not cause any events so we dont need it).
                delayBehChanges a0 (c0@(JustAfter t1, _) : c1@(bt2, _) : cs)
                    | t1 == btTime bt2  = delayBehChanges  a0 (c0 : cs)
                    | otherwise         = c0 : delayBehChanges a0 (c1 : cs)
                delayBehChanges a0 (c0@(JustAfter _, _) : [])
                    = c0 : delayBehChanges a0 []

                apB :: [(BehTime, (j -> k))] -> [(BehTime, j)] -> [(BehTime, k)]
                apB [] _ = []
                apB _ [] = []
                apB tffs@((tf0,f0):_) taas@((ta0,a0):_)
                    = case tf0 `compare` ta0 of
                        EQ -> apB' True  tffs True  taas
                        LT -> apB' False tffs True  taas
                        GT -> apB' True  tffs False taas

                -- "current time" is newer of 2 head times
                -- Bool's are true if value is known at current time
                apB' :: Bool -> [(BehTime, (j -> k))]
                     -> Bool -> [(BehTime,  j      )]
                     ->         [(BehTime,       k )]
                apB' _ [] _ _ = []
                apB' _ _ _ [] = []
                apB' f00May tffs@((tf0,f0):f1's) a00May taas@((ta0,a0):a1's)
                    = case tf0 `compare` ta0 of
                        EQ -> (ta0, f0 a0) : apB' True f1's
                                                  True a1's
                        -- Current time is ta0
                        LT -> if f00May
                            then (ta0, f0 a0) : apB' True  tffs True  a1's
                            else                apB' False tffs True  a1's

                        -- Current time is tf0
                        GT -> if a00May
                            then (tf0, f0 a0) : apB' True  f1's True  taas
                            else                apB' True  f1's False taas

        lcEvts' :: EventIx a -> Maybe (GateRep Time a)
        lcEvts' eix = case updateWay myNode e of
            NoUpdate       -> Nothing
            LocalUpdate    -> fromUpdatesList
            RemoteUpdate   -> fromUpdatesList
            DerivedUpdate  -> case e of
                -- Nothing for source event even if it is local, because we will get this as an Update.
                Source {}                    -> error "Source Event cannot be derived."
                EIx _ _                        -> error "Unexpected EIx"
                SendE _ _ (toEix -> eix')    -> lcEvts lc' eix'
                MapE _ f (toEix -> eA)
                    -> case lcEvts' eA of
                        Nothing -> Nothing
                        Just (GateRep maxT updates) -> Just (GateRep maxT (fmap f <$> updates))
                Sample _ f (toBix -> bix) (toEix -> eA)
                    -> do
                        GateRep maxTB _updatesB <- lcBehs lc' bix
                        GateRep maxTE updatesE  <- lcEvts lc' eA
                        let maxT' = minTimeBehTime maxTE maxTB
                            updates' = [ (sampleT, f sampleT bVal eVal)
                                            | (sampleT, eVal) <- dropUntilTime maxT' updatesE
                                            , let bVal = lcBehVal lc' (Exactly sampleT) bix ]
                        return $ GateRep maxT' updates'


            where
                e = circEvt c eix
                fromUpdatesList = findEvtUpdates eix <> lcEvts lc eix

        findGateUpdates :: (UpdateList -> Maybe (GateRep t a)) -> Maybe (GateRep t a)
        findGateUpdates changesMay = case mapMaybe changesMay ups of
            [] -> Nothing
            [x] -> Just x
            _ -> error "Currently don't support multiple update lists on the same gate."

        findEvtUpdates :: EventIx a -> Maybe (GateRep Time a)
        findEvtUpdates eix = findGateUpdates changesMay
            where
                changesMay (UpdateListB (BehaviorIx _v :: BehaviorIx va) _maxT _vChanges) = Nothing
                changesMay (UpdateListE (EventIx    v  :: EventIx   va) maxT vEvents)
                    | v == eixVert eix  = let updates = unsafeCoerce vEvents
                                            in if null updates then Nothing else Just $ GateRep maxT updates
                    | otherwise = Nothing

        findBehUpdates :: BehaviorIx a -> Maybe (GateRep BehTime a)
        findBehUpdates bix = findGateUpdates changesMay
            where
                changesMay (UpdateListE (EventIx    _v  :: EventIx   va) _maxT _vEvents) = Nothing
                changesMay (UpdateListB (BehaviorIx v :: BehaviorIx va) maxT vChanges)
                    | v == bixVert bix  = let updates = unsafeCoerce vChanges
                                            in if null updates then Nothing else Just $ GateRep maxT updates
                    | otherwise = Nothing

-- Asserting on LiveCircuitls
lintLiveCircuit :: LiveCircuit node -> LiveCircuit node
lintLiveCircuit = id -- TODO



-- Combinators

-- accumE :: a -> Event os (a -> a) -> Event os a
-- accumE a0 accE = withDelay a0 $ \ prevValB
--     -> Step a0 (Sample (\ _time prevVal acc -> acc prevVal) prevValB accE)

withDelay :: (node ~ MomentNode mt, NodeC (MomentNode mt))
          => a -> (Behavior node a -> Moment mt (Behavior node a, r)) -> Moment mt r
withDelay a0 withDelayF = mdo
    bD <- beh $ Delay (owners b) a0 b
    (b,r) <- withDelayF bD
    return r

-- accumB :: a -> Event os (a -> a) -> Moment mt (Behavior node a)
-- accumB a0 accE = withDelay a0 $ \ prevValB -> do
--     let beh = Step a0 $ Sample (\ _time prevVal acc -> acc prevVal) prevValB accE
--     return (beh, beh)
-- accumB a0 updateE = Step a0 <$> accumE a0 updateE
{-

accumE :: (Typeable a, NodeC (MomentNode mt), MomentTypes mt)
       => a -> Event os (a -> a) -> Moment mt (Event os a)
accumE a0 updateE = withDelay a0 $ \ aD -> do
    aE <- evt $ Sample (\ _time a' updater -> updater a') aD updateE
    aB <- beh $ Step a0 aE
    return (aB, aE)
-}
