{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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

-- | An event style map. Represents a partial mapping from time to events (see lookupEMap).
newtype EMap a = EMap { emapToBMap :: BMap (Maybe a) }
    -- ^ EMap Has the invariant that all known values of Just anything must be
    -- at a Time (i.e. not TimeDI) and must be instantaneous i.e. be followed
    -- immediately (DI_JustAfter) by a unknown or a known Nothing.
    deriving (Functor)

instance GateMap EMap where
    gateNull = gateNull . emapToBMap
    takeFrom minTInc = EMap . takeFrom minTInc . emapToBMap
    gateMaxT = gateMaxT . emapToBMap
    union a b = EMap $ union (emapToBMap a) (emapToBMap b)

-- -- | Zip emaps.
-- zipEMap
--     :: _
--     -> EMap a
--     -> EMap b
--     -> EMap c
-- zipEMap f emapA emapB = EMap $ zipBMap f (emapToBMap emapA) (emapToBMap emapB)