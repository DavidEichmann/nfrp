{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE RankNTypes #-}
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

module LiveCircuit where

import Control.Exception.Base (assert)
import Control.Monad (when)
import Data.Kind
import Data.Maybe (fromMaybe, mapMaybe)
import Data.List (find)
import qualified Data.Map as Map
import Unsafe.Coerce

import Circuit
import Time
import GateRep

data LiveCircuit node = LiveCircuit
    { lcCircuit :: Circuit node

    -- These are Nothing if no data is available.
    -- If Just, knowlage is complete from time=0. I.e. minT=0.
    , lcBehs :: forall a . BehaviorIx a -> Maybe (BMap a)
    , lcEvts :: forall a . EventIx    a -> Maybe (EMap a)

    , lcNode :: node
             -- ^ What node the circuit is running on.
    }

-- lcBehChanges  :: LiveCircuit node -> BehaviorIx a -> [(TimeDI, a)]
-- lcBehChanges circuit bix = maybe [] grepChanges (lcBehs circuit bix)

-- lcEvents      :: LiveCircuit node -> EventIx a -> [(Time, a)]
-- lcEvents     circuit eix = maybe [] grepChanges (lcEvts circuit eix)

lcGateMaxT :: NodeC node => LiveCircuit node -> GateIx a -> Maybe TimeDI
lcGateMaxT lc (GateIxB b) = lcBehMaxT lc b
lcGateMaxT lc (GateIxE e) = lcEvtMaxT lc e

lcBehMaxT :: NodeC node => LiveCircuit node -> BehaviorIx a -> Maybe TimeDI
lcBehMaxT lc bix = gateMaxT =<< lcBehs lc bix

lcEvtMaxT :: NodeC node => LiveCircuit node -> EventIx a -> Maybe TimeDI
lcEvtMaxT lc eix = gateMaxT =<< lcEvts lc eix

lcBehVal :: NodeC node => LiveCircuit node -> TimeDI -> BehaviorIx a -> a
lcBehVal lc t bix = let
    bmap = fromMaybe
            (error $ "Trying to access behavior value at time " ++ show t
                    ++ " but no values are known for the behavior")
            (lcBehs lc bix)
    in lookupBMapErr "in lcBehVal" t bmap

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
                        Const _ val    -> Just (UpdateListB bix (constBMap 0 val))
                        Delay _ _ _    -> Nothing
                        Step _ val0 _  -> Just (UpdateListB bix (instantaneousBMap 0 val0))
                        MapB _ _ _     -> Nothing
                        Ap _ _ _       -> Nothing
                        SendB _ _ _    -> Nothing
                _ -> Nothing
            )
            (Map.elems (circGateIxs c))

-- Transactionally update the circuit. Returns (new live circuit, changed behaviors/events (lcBehMaxT has increased))
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
                go :: gix
                   -> (LiveCircuit node -> Maybe (gmap a))
                   -> (gix -> gmap a -> UpdateList)
                   -> Maybe UpdateList
                go ix lcGate mkUpdateList = case (lcGate lc, lcGate lc') of
                    (Nothing, Nothing)
                        -> Nothing
                    (Nothing, Just gmap)
                        -> Just $ mkUpdateList ix gmap
                    ( Just gmap, Just gmap' )
                        -> let  -- This is the difference of the old and new. it assumes that
                                -- the new is just the old with some chronologially newer info.
                                -- TODO do we ever need to support the case that information "from
                                -- the past" is gained?
                                diffIsh = case (gateMaxT gmap, gateMaxT gmap') of -- maxT < maxT'
                                    (Nothing, Nothing) -> Nothing
                                    (Just _, Nothing) -> lostAllGateInfoErr
                                    (Nothing, Just _) -> Just gmap'
                                    (Just maxT, Just maxT')
                                        | maxT == maxT' -> Nothing
                                        | otherwise     -> Just (takeFrom (delayTime maxT) gmap)
                                                    -- ^ TODO the inability to
                                                    -- delay an already delayed
                                                    -- time may cause issue
                                                    -- here: we may end up
                                                    -- returning the old latest
                                                    -- value even if it was
                                                    -- already detected as
                                                    -- change in a previous
                                                    -- iteration.
                                                    -- On second thought I think this may be alright (intuitively).
                                maxTMay  = gateMaxT gmap
                                maxTMay' = gateMaxT gmap'
                            in mkUpdateList ix <$> diffIsh
                    (Just _, Nothing) -> lostAllGateInfoErr
                lostAllGateInfoErr = error "Impossible! Somehow we lost all info about a gate."
                in
                    case gix of
                        (GateIxB bix) -> go bix (flip lcBehs bix) UpdateListB
                        (GateIxE eix) -> go eix (flip lcEvts eix) UpdateListE
                )
            $ Map.elems (circGateIxs c)

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
                    UpdateListB b bmap -> case lcBehMaxT lc b of
                        Nothing -> True
                        Just maxTOld -> gateMinT bmap > Just maxTOld
                    UpdateListE e emap -> case lcEvtMaxT lc e of
                        Nothing -> True
                        Just maxTOld -> gateMinT emap > Just maxTOld)
                changes)

        -- TODO asset that all updates are after their corresponding Event/Behavior's MaxT time.
        --      we have at most 1 UpdateList per gate

        c = lcCircuit lc

        -- Assumption (A): since we assuem that we get complete and inorder info about each "remote" gate from a
        -- unique remote node, we can immediatelly increase lcBehMaxT and know that the value hasn't changed
        -- sine the previous update we received. Likewise we can be sure that there are no earlier events that we
        -- have missed.

        -- TODO/NOTE this is super inefficient
        lcBehs' :: BehaviorIx a -> Maybe (BMap a)
        lcBehs' bix = case updateWay myNode b of
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
                        Just eventEMap
                            -> Just $ GateRep
                                maxTE
                                (((\ (t, val) -> (DI_Exactly t, val)) <$> es) ++ [(DI_Exactly 0, a0)])
                                minTE
                MapB _ f (toBix -> bixParent)
                    -> fmap f <$> (lcBehs lc' bixParent)
                Ap _ (toBix -> bixF) (toBix -> bixArg)
                    -> do
                        fBMap   <- lcBehs lc' bixF
                        argBMap <- lcBehs lc' bixArg
                        when (minTF /= minTArg)
                            (error $ "TODO support Ap of Bheaviors with unequal minT ("
                                ++ show minTF ++ " /= " ++ show minTArg ++ ")")
                        let maxT' = min maxTF maxTArg
                            updates' = apB True (dropUntilTime maxT' fUpdates)
                                           True (dropUntilTime maxT' argUpdates)
                        return $ GateRep maxT' updates' minTF
            where
                b = circBeh c bix
                fromUpdatesList = findBehUpdates bix <> lcBehs lc bix

                delayBehRep :: a -> BMap a -> BMap a
                delayBehRep a0 bmap
                    = delayTime bmap `gateUnion` instantaneousBMap 0 a0

                -- Must not have 2 JustAfter t changes in a row (with the same t).
                delayBehChanges :: a -> [(TimeDI, a)] -> [(TimeDI, a)]
                delayBehChanges a0 []
                    = [(DI_Exactly 0, a0)]
                delayBehChanges a0 (c0@(DI_Inf, _) : cs)
                    = c0 : delayBehChanges a0 cs
                delayBehChanges a0 ((DI_Exactly t, a) : cs)
                    = (DI_JustAfter t, a) : delayBehChanges a0 cs
                -- Because it's impossible to sample the JustAfter t value for a JustAfter t  befor it,
                -- we remove it (note it can also not cause any events so we dont need it).
                delayBehChanges a0 (c0@(DI_JustAfter t1, _) : c1@(bt2, _) : cs)
                    | t1 == bt2MajorTime = delayBehChanges  a0 (c0 : cs)
                    | otherwise          = c0 : delayBehChanges a0 (c1 : cs)
                    where
                        bt2MajorTime = case bt2 of
                            DI_Exactly t -> t
                            DI_JustAfter t -> t
                            DI_Inf -> error $ "Behavior changes our of order. Found DI_Inf occuring before " ++ show (fst c0)
                delayBehChanges a0 (c0@(DI_JustAfter _, _) : [])
                    = c0 : delayBehChanges a0 []

                -- "current time" is newer of 2 head times
                -- Bool's are true if value is known at current time
                apB :: Bool -> [(TimeDI, (j -> k))]
                     -> Bool -> [(TimeDI,  j      )]
                     ->         [(TimeDI,       k )]
                apB _ [] _ _ = []
                apB _ _ _ [] = []
                apB f00May tffs@((tf0,f0):f1's) a00May taas@((ta0,a0):a1's)
                    = case tf0 `compare` ta0 of
                        EQ -> (ta0, f0 a0) : apB True f1's
                                                  True a1's
                        -- Current time is ta0
                        LT -> if f00May
                            then (ta0, f0 a0) : apB True  tffs True  a1's
                            else                apB False tffs True  a1's

                        -- Current time is tf0
                        GT -> if a00May
                            then (tf0, f0 a0) : apB True  f1's True  taas
                            else                apB True  f1's False taas

        lcEvts' :: forall a . EventIx a -> Maybe (EMap a)
        lcEvts' eix = case updateWay myNode e of
            NoUpdate       -> Nothing
            LocalUpdate    -> fromUpdatesList
            RemoteUpdate   -> fromUpdatesList
            DerivedUpdate  -> case e of
                -- Nothing for source event even if it is local, because we will get this as an Update.
                Source {}                    -> error "Source Event cannot be derived."
                EIx _ _                      -> error "Unexpected EIx"
                SendE _ _ (toEix -> eix')    -> lcEvts lc' eix'
                MapE _ f (toEix -> eA)       -> fmap f <$> lcEvts' eA
                Sample _ f (toBix -> bix) (toEix -> eA)
                    -> do
                        updatesBMap <- lcBehs lc' bix
                        updatesEMap  <- lcEvts lc' eA
                        when (minTB > minTE)
                            (error "TODO support (partially) sampling a behavior withe a minT greater than the sampling event's minT.")
                            -- ^ TODO this also requires talking max of minTE and minTB in the def for minT' bellow.
                        let maxT' :: TimeDI
                            maxT' = minTime maxTE maxTB
                            minT' :: TimeD
                            minT' = minTE
                            updates' :: [(Time, a)]
                            updates' = [ (sampleT, f sampleT bVal eVal)
                                            | (sampleT, eVal) <- dropUntilTime maxT' updatesE
                                            , let bVal = lcBehVal lc' (DI_Exactly sampleT) bix ]
                        return $ GateRep maxT' updates' minT'


            where
                e = circEvt c eix
                fromUpdatesList = findEvtUpdates eix <> lcEvts lc eix

        findGateUpdates :: (UpdateList -> Maybe x) -> Maybe x -- ^ Maybe (maxT, updates maybe nul)
        findGateUpdates changesMay = case mapMaybe changesMay ups of
            [] -> Nothing
            [x] -> Just x
            _ -> error "Currently don't support multiple update lists on the same gate."

        findEvtUpdates :: EventIx a -> Maybe (EMap a)
        findEvtUpdates eix = findGateUpdates changesMay
            where
                changesMay (UpdateListB (BehaviorIx _v :: BehaviorIx va) _) = Nothing
                changesMay (UpdateListE (EventIx    v  :: EventIx   va) emap)
                    | v == eixVert eix  = Just (unsafeCoerce emap)
                    | otherwise = Nothing

        findBehUpdates :: BehaviorIx a -> Maybe (BMap a)
        findBehUpdates bix = findGateUpdates changesMay
            where
                changesMay (UpdateListE (EventIx    _v  :: EventIx   va) _) = Nothing
                changesMay (UpdateListB (BehaviorIx v :: BehaviorIx va) bmap)
                    | v == bixVert bix  = Just (unsafeCoerce bmap)
                    | otherwise = Nothing

-- Asserting on LiveCircuitls
lintLiveCircuit :: LiveCircuit node -> LiveCircuit node
lintLiveCircuit = id -- TODO

-- | Index, max time incl., changes, min time incl.
data UpdateList
    = forall a . UpdateListB (BehaviorIx a) (BMap a)
    | forall a . UpdateListE (EventIx    a) (EMap a)

instance Show UpdateList where
    show ul = "UpdateList (" ++ case ul of
                UpdateListB b bmap -> show b ++ ") Max,Min Times=" ++ show (gateMaxT bmap, gateMinT bmap)
                UpdateListE e emap -> show e ++ ") Max,Min Times=" ++ show (gateMaxT emap, gateMinT emap)
