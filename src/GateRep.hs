{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module GateRep
    ( GateMap (..)
    , BMap
    , lookupBMap
    , lookupBMapErr
    , bmapSingleton
    , EMap
    ) where

import Data.Maybe (fromMaybe, isNothing)

import Time

class Functor m => GateMap m where
    -- | True if the map covers 0 time nor zero instantaneous information.
    gateNull :: m a -> Bool
    gateNull = isNothing . gateMaxT
    -- | Get the maximum time of which we have knowlage. Nothing means we have no knowlage.
    gateMaxT :: m a -> Maybe TimeDI
    -- | Take only the data at and after a given time.
    takeFrom :: TimeDI -> m a -> m a
    -- | Combine the knowlage of this gate. Any overlap of time will result in an error.
    union :: m a -> m a -> m a


-- | A behavior style map. Represents a partial mapping from time to value (see lookupBMap).
newtype BMap a = BMap [(TimeDI, Maybe a)]
    -- ^ [(t, aMay: value (if one is known at time midT onwards))]
    -- You can imagine there is an implicit (Nothing, -Infintiy) at the end of the list.
    -- List is in reverse chronological order i.e. for all indexes, i:
    --   t(i) > t(i+1)
    -- No 2 consecutive Nothings
    --   not (isNothing aMay(i) && isNothing aMay(i+1))
    --   not (isNothing last aMay)
    deriving (Functor)

-- | This defines the denotation of BMap
-- Lookup the value of a behavior at a given time.
lookupBMap :: TimeDI -> BMap a -> Maybe a
lookupBMap t (BMap allXs) = go allXs
    where
    go [] = Nothing
    go ((t_i, aMay_i):xs)
        | t >= t_i  = aMay_i
        | otherwise = go xs

instance GateMap BMap where
    gateNull (BMap []) = True
    gateNull _ = False -- Note that the last element in BMap is not Nothing

    takeFrom minTInc (BMap allXs) = BMap (go allXs)
        where
        go [] = []
        go (x@(t, a) : xs) = case compare t minTInc of
            GT -> x : go xs
            EQ -> [x]
            LT -> [(minTInc, a)]

    gateMaxT (BMap []) = Nothing
    gateMaxT (BMap ((t,_):_)) = Just t

    union = zipBMap $ \ aMay bMay -> case (aMay, bMay) of
        (Nothing, Nothing) -> Nothing
        (Just a, Nothing) -> Just a
        (Nothing, Just a) -> Just a
        -- TODO I think this may happen always when taking union of delayed BMaps
        (Just _, Just _) -> error "union: Attempting union on BMaps with overlapping knowlage."


-- | Zip BMaps. Values are combined with the given function.
zipBMap
    :: (Maybe a -> Maybe b -> Maybe c)
    -- ^ Combine values. For both inputs and output, Nothing means unknown value.
    -- Hence this zip function allows you to modify the known time spans.
    -> BMap a
    -> BMap b
    -> BMap c
zipBMap f (BMap allAs) (BMap allBs) = BMap (go allAs allBs)
    where
    go as [] = (\(t,aMay) -> (t, f aMay Nothing)) <$> as
    go [] bs = (\(t,bMay) -> (t, f Nothing bMay)) <$> bs
    go aas@((ta,aMay):as) bbs@((tb,bMay):bs) = let cMay = f aMay bMay
        in case compare ta tb of
            LT -> (tb, cMay) : go aas bs
            EQ -> (ta, cMay) : go as bs
            GT -> (ta, cMay) : go as bbs

instance DelayTime (BMap a) where
    -- | You'll likely want to add an instantenious value at time 0 after
    -- applying this delay.
    delayTime (BMap xs) = BMap ((\(t,a) -> (delayTime t, a)) <$> xs)


bmapSingleton :: TimeDI -> TimeDI -> a -> BMap a
bmapSingleton start stop value = BMap [(delayTime stop, Nothing), (start, Just value)]

lookupBMapErr :: String -> TimeDI -> BMap a -> a
lookupBMapErr err t bmap = case lookupBMap t bmap of
    Nothing -> error $ "lookupBMapErr: time out of bounds: " ++ err
    Just a -> a

-- | Is a value known. Usually used inrelation to a span of time.
data KnownState
    = Known
    | Unknown
    deriving (Eq)
data EMapEl a
    = OccurKnown Time a
    -- ^ An event occurence and an implied Know state change/continuation.
    | Knowlage TimeDI KnownState
    -- ^ Change of known/unknown state.
    deriving (Functor)

emapElTime :: EMapEl a -> TimeDI
emapElTime (OccurKnown t _) = toTime t
emapElTime (Knowlage t _) = t

emapElKnownState :: EMapEl a -> KnownState
emapElKnownState (OccurKnown _ _) = Known
emapElKnownState (Knowlage _ k) = k

emapElKnownVariantAndEqual :: EMapEl a -> EMapEl a -> Bool
emapElKnownVariantAndEqual (Knowlage t1 k1) (Knowlage t2 k2) = t1 == t2 && k1 == k2
emapElKnownVariantAndEqual _ _ = False

-- | An event style map. Represents a partial mapping from time to events (see lookupEMap).
newtype EMap a = EMap [EMapEl a]
    -- ^ EMap
    -- You can imagine there is an implicit (Knowlage (-Infintiy) Unknown) at the end of the list.
    -- Invariants:
    --   * List is in reverse chronological order.
    --     time(i) > time(i+1)
    --   * Hence the list is empty or ends with a change to Known state.
    --   * there are no consecutive Know nor consecutive Unknonw elements of the Knowlage variant.
    --   * there are no Knowlage Know elements directly after OccurKnown elements.
    deriving (Functor)

-- | Create an EMap from the underlying list. Returns Nothing if invalid (see EMap documentation for invariants).
emap :: [EMapEl a] -> Maybe (EMap a)
emap allXs = if isValid allXs then Just (EMap allXs) else Nothing
    where
    isValid [] = True
    isValid [x] = emapElKnownState x == Known
    -- No Knowlage Known after Occurs.
    isValid (Knowlage _ Known : OccurKnown _ _ : _) = False
    -- No consecutive equal Knowlage variant entries.
    isValid (Knowlage _ ks1 : Knowlage _ ks2 : _) | ks1 == ks2 = False
    -- Strictly increasing time
    isValid (x : y : _) | emapElTime x <= emapElTime y = False
    -- Ok so far, check the tail.
    isValid (_:xs) = isValid xs

-- TODO you could use the representation I started in the more_complicated_EMap
-- to facilitate writing code that generates correct EMaps by construction

-- | Create an EMap from the underlying list, but also remove consecutive
-- Knowlage elements of equal Knowlage State. Errors is time is not strictly decreasing.
emapCleanupErr :: [EMapEl a] -> EMap a
emapCleanupErr = EMap . clean
    where

    clean [] = []
    -- Last element has Know state. Unknown state is resundant.
    clean [x@(Knowlage _ Unknown)] = []
    clean [x] = [x]
    -- Knowlage Known after Occurs is redundant
    clean (Knowlage _ Known : xs@(OccurKnown _ _ : _)) = clean xs
    -- Consecutive equal Knowlage variants entries are redundant.
    -- If Knowlage state is equal, redundancy is clear.
    -- Else knowlage state is unequal, so we have a left bias. This is a bit ugly but uself.
    clean (x@(Knowlage _ ks1) : Knowlage _ ks2 : xs) = clean (x:xs)
    -- Strictly increasing time
    clean (x : y : _) | emapElTime x <= emapElTime y = error "emapCleanupErr: time is not strictly increasing."
    -- Ok so far, clean the tail.
    clean (x:xs) = x : clean xs

instance GateMap EMap where
    gateNull (EMap []) = True
    gateNull _ = False  -- ^ The only other gateNull case is a list of only Stop values,
                    -- but that is not a valid EMap, so we dont Check (it must
                    -- be empty of end in a Start).

    takeFrom minTInc (EMap allXs) = emapCleanupErr (go allXs)
        where
        go [] = []
        go (x:xs) = case x of
            Knowlage t knownState -> case compare t minTInc of
                GT -> x : go xs
                EQ -> [x]
                LT -> case knownState of
                        Known -> [Knowlage minTInc Known]
                        Unknown -> [] -- Unknown state at the end is implicit.
            OccurKnown t _ -> let tDI = toTime t in case compare tDI minTInc of
                GT -> x : go xs
                EQ -> [x]
                LT -> [Knowlage minTInc Known]

    gateMaxT (EMap []) = Nothing
    gateMaxT (EMap (Knowlage t Unknown : _)) = Just t
    gateMaxT (EMap (Knowlage _ Known   : _)) = Just DI_Inf
    gateMaxT (EMap (OccurKnown _ _     : _)) = Just DI_Inf

    union = zipEMap _
    --   (\ mayMayA mayMayB -> case (mayMayA, mayMayB) of
    --     (Just aMay, Nothing) -> Just aMay
    --     (Nothing, Just bMay) -> Just bMay
    --     (Nothing, Nothing) -> Nothing
    --     (Just _, Just _) -> error "union: Attempting union on BMaps with overlapping knowlage."
    --     )

emapToBmap :: EMap

-- | Zip emaps.
zipEMap
    :: (EMapSample a -> EMapSample b -> EMapSample c)
    -- ^ Combine values. For both inputs and output, Nothing means unknown events.
    -- Hence this zip function allows you to modify the known time spans.
    -- If you think of events as behaviors of maybe a value, then this makes more intuitive sense.
    -> EMap a
    -> EMap b
    -> EMap c
zipEMap f (EMap allAs) (EMap allBs) = emapCleanupErr $ go allAs allBs
    where
    go as [] = map
                    _
                    -- (\case
                    --     OccurKnown t a ->

                    --     Start t -> Start t
                    --     StartOccur (t, a) -> case f (Just (Just a)) Nothing of
                    --             Just (Just c) -> StartOccur (t, c)
                    --             Just Nothing -> Start (toTime t)
                    --             Nothing -> Start (toTime t)
                    --     Stop t -> Stop t
                    --     StopOccur (t, a) -> case f (Just (Just a)) Nothing of
                    --             Just (Just c) -> StopOccur (t, c)
                    --             Just Nothing -> Stop (toTime t)
                    --             Nothing -> Stop (toTime t)
                    -- )
                    as
    go [] bs = map
                    _
                    -- (\case
                    --     Start t -> Start t
                    --     StartOccur (t, b) -> case f Nothing (Just (Just b)) of
                    --             Just (Just c) -> StartOccur (t, c)
                    --             Just Nothing -> Start (toTime t)
                    --             Nothing -> Start (toTime t)
                    --     Stop t -> Stop t
                    --     StopOccur (t, b) -> case f Nothing (Just (Just b)) of
                    --             Just (Just c) -> StopOccur (t, c)
                    --             Just Nothing -> Stop (toTime t)
                    --             Nothing -> Stop (toTime t)
                    -- )
                    bs
    go (a:as) (b:bs) = case compare ta tb of
        LT -> _
        EQ -> _
        GT -> _
        where
        ta = emapElTime a
        tb = emapElTime b
