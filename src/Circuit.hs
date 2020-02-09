{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
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

module Circuit where

import Control.Monad.State
import Unsafe.Coerce
import Data.Kind
import Data.Dynamic
import qualified Data.List as List
import qualified Data.Graph as Graph
import qualified Data.Map as Map

import Time

-- Some common constraint type families
type family NodeC node :: Constraint where
    NodeC node =
        ( Eq node
        , Show node
        , Ord node
        , Typeable node
        -- , ReifySomeNode node
        )

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
    . Listener (MomentNode mt) (BehaviorIx a) (MomentCtx mt -> a -> TimeDI -> IO ())

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
        => (MomentNode mt) -> Behavior (MomentNode mt) a -> (MomentCtx mt -> a -> TimeDI -> IO ()) -> Moment mt ()
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