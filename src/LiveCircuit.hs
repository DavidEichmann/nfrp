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

import Unsafe.Coerce
import Data.Kind
import Data.Maybe (mapMaybe)
import Data.List (find)
import qualified Data.Map as Map


import Control.Exception.Base (assert)

import Circuit
import Time
import GateRep

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
                            in if maxT < maxT'
                                then Just $ mkUpdateList ix maxT' newUpdates
                                else Nothing
                    (Just _, Nothing) -> error "Impossible! Somehow we lost all info about a gate."
                in
                    case gix of
                        (GateIxB bix) -> go bix (flip lcBehs bix) UpdateListB
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
                            updates' = apB True (dropUntilTime maxT' fUpdates)
                                            True (dropUntilTime maxT' argUpdates)
                        return $ GateRep maxT' updates'
            where
                b = circBeh c bix
                fromUpdatesList = updateGateRep (findBehUpdates bix) (lcBehs lc bix)

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

                -- "current time" is newer of 2 head times
                -- Bool's are true if value is known at current time
                apB :: Bool -> [(BehTime, (j -> k))]
                     -> Bool -> [(BehTime,  j      )]
                     ->         [(BehTime,       k )]
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
                fromUpdatesList = updateGateRep (findEvtUpdates eix) (lcEvts lc eix)



        updateGateRep :: Maybe (t, [(t, a)]) -> Maybe (GateRep t a) -> Maybe (GateRep t a)
        updateGateRep Nothing Nothing = Nothing
        updateGateRep Nothing x = x
        updateGateRep (Just (maxT, us)) Nothing
            = Just $ GateRep maxT us
        updateGateRep (Just (maxT', us')) (Just (GateRep _maxT us))
            = Just $ GateRep maxT' (us' ++ us)

        findGateUpdates :: (UpdateList -> Maybe (t, [(t, a)])) -> Maybe (t, [(t, a)]) -- ^ Maybe (maxT, updates maybe nul)
        findGateUpdates changesMay = case mapMaybe changesMay ups of
            [] -> Nothing
            [x] -> Just x
            _ -> error "Currently don't support multiple update lists on the same gate."

        findEvtUpdates :: EventIx a -> Maybe (Time, [(Time, a)])
        findEvtUpdates eix = findGateUpdates changesMay
            where
                changesMay (UpdateListB (BehaviorIx _v :: BehaviorIx va) _maxT _vChanges) = Nothing
                changesMay (UpdateListE (EventIx    v  :: EventIx   va) maxT vEvents)
                    | v == eixVert eix  = Just (maxT, unsafeCoerce vEvents)
                    | otherwise = Nothing

        findBehUpdates :: BehaviorIx a -> Maybe (BehTime, [(BehTime, a)])
        findBehUpdates bix = findGateUpdates changesMay
            where
                changesMay (UpdateListE (EventIx    _v  :: EventIx   va) _maxT _vEvents) = Nothing
                changesMay (UpdateListB (BehaviorIx v :: BehaviorIx va) maxT vChanges)
                    | v == bixVert bix  = Just (maxT, unsafeCoerce vChanges)
                    | otherwise = Nothing

-- Asserting on LiveCircuitls
lintLiveCircuit :: LiveCircuit node -> LiveCircuit node
lintLiveCircuit = id -- TODO

data UpdateList
    = forall a . UpdateListB (BehaviorIx a) BehTime [(BehTime, a)]
    | forall a . UpdateListE (EventIx    a) Time    [(Time, a)]

instance Show UpdateList where
    show ul = "UpdateList (" ++ case ul of
                UpdateListB b maxT us -> show b ++ ") Times=" ++ show (maxT, fst <$> us)
                UpdateListE e maxT us -> show e ++ ") Times=" ++ show (maxT, fst <$> us)
