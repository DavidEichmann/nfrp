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

import Data.Maybe (isNothing)

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

data EMapEl a
    = Start TimeDI
    -- ^ Known time span starts.
    -- Interpreting `EMap a` as `BMap (Maybe a)`, this can be thought of as a
    -- BMap list entry of `[..., (t, Just Nothing),
    -- ...]`.
    | StartOccur (Time, a)
    -- ^ Known time span starts/continues with a value occurence.
    | Stop TimeDI
    -- ^ Known time span stops.
    | StopOccur (Time, a)
    -- ^ Known time span stops with a value occurence. If directly after a
    -- Stop/StopOccur, then this is an instantenious span of knowlage.
    deriving (Functor)

emapElTime :: EMapEl a -> TimeDI
emapElTime (Start t) = t
emapElTime (StartOccur (t, _)) = toTime t
emapElTime (Stop t) = t
emapElTime (StopOccur (t, _)) = toTime t

-- | An event style map. Represents a partial mapping from time to events (see lookupEMap).
newtype EMap a = EMap [EMapEl a]
    -- ^ EMap
    -- You can imagine there is an implicit (Stop -Infintiy) at the end of the list.
    -- List is in reverse chronological order.
    -- Hence the list is empty or ends with a Start/StartOccur value and
    -- there are no consecutive Starts nor consecutive Stops (though occur versions my repeate).
    --   time(i) > time(i+1)
    deriving (Functor)

instance GateMap EMap where
    gateNull (EMap []) = True
    gateNull _ = False  -- ^ The only other gateNull case is a list of only Stop values,
                    -- but that is not a valid EMap, so we dont Check (it must
                    -- be empty of end in a Start).

    takeFrom minTInc (EMap allXs) = EMap (go allXs)
        where
        go [] = []
        go (x:xs) = case x of
            Start t -> case compare t minTInc of
                GT -> x : go xs
                EQ -> [x]
                LT -> [Start minTInc]
            StartOccur (t, _) -> let tDI = toTime t in case compare tDI minTInc of
                GT -> x : go xs
                EQ -> [x]
                LT -> [Start minTInc]
            Stop t -> case compare t minTInc of
                GT -> x: go xs
                -- Stop is implicit
                EQ -> []
                LT -> []
            StopOccur (t, _) -> let tDI = toTime t in case compare tDI minTInc of
                GT -> x : go xs
                EQ -> [x]
                LT -> [Start minTInc]

    gateMaxT (EMap []) = Nothing
    gateMaxT (EMap (x:_)) = Just $ emapElTime x

    union = zipEMap (\ mayMayA mayMayB -> case (mayMayA, mayMayB) of
        (Just aMay, Nothing) -> Just aMay
        (Nothing, Just bMay) -> Just bMay
        (Nothing, Nothing) -> Nothing
        (Just _, Just _) -> error "union: Attempting union on BMaps with overlapping knowlage."
        )

-- | Zip emaps.
zipEMap
    :: (Maybe (Maybe a) -> Maybe (Maybe b) -> Maybe (Maybe c))
    -- ^ Combine values. For both inputs and output, Nothing means unknown events.
    -- Hence this zip function allows you to modify the known time spans.
    -- If you think of events as behaviors of maybe a value, then this makes more intuitive sense.
    -> EMap a
    -> EMap b
    -> EMap c
zipEMap f (EMap allAs) (EMap allBs) = EMap (cleanup $ go allAs allBs)
    where
    go as [] = map
                    (\case
                        Start t -> Start t
                        StartOccur (t, a) -> case f (Just (Just a)) Nothing of
                                Just (Just c) -> StartOccur (t, c)
                                Just Nothing -> Start (toTime t)
                                Nothing -> Start (toTime t)
                        Stop t -> Stop t
                        StopOccur (t, a) -> case f (Just (Just a)) Nothing of
                                Just (Just c) -> StopOccur (t, c)
                                Just Nothing -> Stop (toTime t)
                                Nothing -> Stop (toTime t)
                    )
                    as
    go [] bs = map
                    (\case
                        Start t -> Start t
                        StartOccur (t, b) -> case f Nothing (Just (Just b)) of
                                Just (Just c) -> StartOccur (t, c)
                                Just Nothing -> Start (toTime t)
                                Nothing -> Start (toTime t)
                        Stop t -> Stop t
                        StopOccur (t, b) -> case f Nothing (Just (Just b)) of
                                Just (Just c) -> StopOccur (t, c)
                                Just Nothing -> Stop (toTime t)
                                Nothing -> Stop (toTime t)
                    )
                    bs
    go (a:as) (b:bs) = case compare ta tb of
        LT -> _
        EQ -> _
        GT -> _
        where
        ta = emapElTime a
        tb = emapElTime b

    -- | Remove consecutive Starts and Stops.
    cleanup :: [EMapEl c] -> [EMapEl c]
    cleanup = _
