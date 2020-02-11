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
    , instantaneousBMap
    , constBMap
    , spanBMap
    , zipBMap
    , headBMap
    , EMap
    , instantaneousEMap
    , spanEMap
    , stepEMap
    , delayStepEMapWithExtra
    , sampleEMap
    ) where

import Data.Maybe (isNothing)

import Time

class (Functor m) => GateMap m where
    -- | True if the map covers 0 time nor zero instantaneous information.
    gateNull :: m a -> Bool
    gateNull = isNothing . gateMaxT
    -- | Get the maximum time of which we have knowlage. Nothing means we have no knowlage.
    gateMaxT :: m a -> Maybe TimeDI
    -- | Get the minimum time of which we have knowlage. Nothing means we have no knowlage.
    gateMinT :: m a -> Maybe TimeDI
    -- | Take only the data at and after a given time.
    takeFrom :: TimeDI -> m a -> m a
    -- | Combine the knowlage of this gate. Any overlap of time will result in an error.
    gateUnion :: m a -> m a -> m a

-- | A behavior style map. Represents a partial mapping from time to value (see lookupBMap).
newtype BMap a = BMap { unBMap :: [(TimeDI, Maybe a)] }
    -- ^ [(t, aMay: value (if one is known at time midT onwards))]
    -- You can imagine there is an implicit (Nothing, -Infintiy) at the end of the list.
    -- Invariants:
    --   * Strictly decreasing time:  t(i) > t(i+1)
    --   * No 2 consecutive Nothings
    --   * Final element (if exists) must be a Just
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

-- | One moment of knowlage.
-- knowlage: exactly t and no other time.
instantaneousBMap :: Time -> a -> BMap a
instantaneousBMap t a = BMap [(DI_JustAfter t, Nothing), (DI_Exactly t, Just a)]

-- | A single value spanning some time
-- knowlage: exactly t and no other time.
spanBMap
    :: TimeDI
    -- ^ When the value starts.
    -> a
    -- ^ The value.
    -> TimeDI
    -- ^ When the knowlage of this value ends.
    -> BMap a
spanBMap startTime _ endTime
    | startTime > endTime
    = error "spanBMap: start time > end time."
spanBMap startTime value endTime
    = BMap [(endTime, Nothing),(startTime, Just value)]

-- | Constant value.
-- knowlage: t to Infinity
constBMap :: Time -> a -> BMap a
constBMap t a = BMap [(DI_Exactly t, Just a)]

instance Semigroup (BMap a) where
    (<>) = gateUnion

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

    gateMaxT bmap = fst <$> headBMap bmap

    gateMinT (BMap []) = Nothing
    gateMinT (BMap xs) = Just (fst (last xs))

    gateUnion = zipBMap $ \ aMay bMay -> case (aMay, bMay) of
        (Nothing, Nothing) -> Nothing
        (Just a, Nothing) -> Just a
        (Nothing, Just a) -> Just a
        -- TODO I think this may happen always when taking gateUnion of delayed BMaps
        (Just _, Just _) -> error "gateUnion: Attempting gateUnion on BMaps with overlapping knowlage."

-- | Get the latest know value (if any is known) and the corresponding maxT.
headBMap :: BMap a -> Maybe (TimeDI, a)
headBMap (BMap []) = Nothing
headBMap (BMap ((t1, Nothing):(_, Just a):_)) = Just (maxT, a)
    where
    maxT = case t1 of
        DI_JustAfter t1' -> DI_Exactly t1'
        DI_Inf -> DI_Inf
        DI_Exactly t1' ->
            error $ "headBMap: Oh shit! You've run into a fundamental problem here. "
            ++ "we can't calculate MaxT, as it is technically equal to \"Just Before "
            ++ show t1' ++ "\", which we don't actually support yet. You may need a new "
            ++ "time type, but perhaps one just used for MaxT? I.e. not used in BMap's representation."
headBMap (BMap ((_, Just a):_)) = Just (DI_Inf, a)
headBMap (BMap ((_, Nothing):(_, Nothing):_)) = error "headBMap: violated BMap invariant: consecutinve Nothings"
headBMap (BMap [(_, Nothing)]) = error "headBMap: violated BMap invariant: last element is Nothing"

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

-- | Create a BMap from a list with fewer invariants:
--
--   * Strictly decreasing time:  t(i) > t(i+1)
--        * With the exception of JustAfter times which may be consecutivelly
--          equal.
--
-- This is checked and an error is returned at that time. TODO we can actually
-- continue processing but leave an error in the middle. These invariants are
-- lifted:
--
--   * JustAfter elements may have equal time. Left most element is chosen.
--   * No 2 consecutive Nothings
--   * Final element (if exists) must be a Just
--
cleanBMapErr :: String -> [(TimeDI, Maybe a)] -> BMap a
cleanBMapErr errMsg allXs = BMap (clean allXs)
    where
    clean [] = []
    -- Final element (if exists) must be a Just
    clean [(_, Nothing)] = []
    clean [x] = [x]
    -- JustAfter elements may have equal time. Left most element is chosen.
    clean (x1@(DI_JustAfter t1, _) : (DI_JustAfter t2,_) : xs)
        | t1 == t2 = clean (x1:xs)
    -- Otherwise strictly decreasing time
    clean ((t1,_) : (t2, _) : _)
        | t1 <= t2 = error $ "cleanBMapErr: expected strictly decreasing time: " ++ errMsg
    -- No 2 consecutive Nothings
    clean ((_, Nothing) : xs@((_, Nothing) : _)) = clean xs
    clean (x:xs) = x : clean xs


instance DelayTime (BMap a) where
    -- | You'll likely want to add an instantenious value at time 0 after
    -- applying this delay.
    delayTime (BMap allXs) = cleanBMapErr "delayTime" ((\(t,a) -> (delayTime t, a)) <$> allXs)

lookupBMapErr :: String -> TimeDI -> BMap a -> a
lookupBMapErr err t bmap = case lookupBMap t bmap of
    Nothing -> error $ "lookupBMapErr: time out of bounds: " ++ err
    Just a -> a

-- | An event style map. Represents a partial mapping from time to events (see lookupEMap).
newtype EMap a = EMap { emapToBMap :: BMap (Maybe a) }
    -- ^ Invariants:
    --   * All known values of Just anything must be at a Time (i.e. not JustAfter or Infintiy)
    --   * All known values of Just anything must be instantaneous i.e. be
    --     followed immediately (DI_JustAfter) by a unknown or a known Nothing.
    --   * All the regular BMap invariants.
    --
    -- NOTE we want to maintain the invariant that Event's cannot be delayed, so
    -- one must be careful not to do e.g. `EMap . delayTime . empToBMap`. Hence
    -- empToBMap is not exported.
    deriving (Functor)

instance Semigroup (EMap a) where
    (<>) = gateUnion

instance GateMap EMap where
    gateNull = gateNull . emapToBMap
    takeFrom minTInc = EMap . takeFrom minTInc . emapToBMap
    gateMaxT = gateMaxT . emapToBMap
    gateMinT = gateMinT . emapToBMap
    gateUnion a b = EMap $ gateUnion (emapToBMap a) (emapToBMap b)

-- | Create a EMap from a list with fewer invariants:
--
--   * cleanBMapErr invariants:
--      * Strictly decreasing time:  t(i) > t(i+1)
--        * With the exception of JustAfter times which may be consecutivelly
--          equal.
--   * All known values of Just anything must be at a Time (i.e. not JustAfter or Infintiy)
--   * All known values of Just anything must be instantaneous i.e. be
--     followed immediately (DI_JustAfter) by a unknown or a known Nothing.
--
-- This is checked and an error is returned at that time. TODO we can actually
-- See cleanBMapErr for lifted invariants
--
cleanEMapErr :: String -> [(TimeDI, Maybe (Maybe a))] -> EMap a
cleanEMapErr errMsg allXs
    = EMap
    $ cleanBMapErr ("cleanBMapErr: " ++ errMsg)
    $ check allXs -- Note we do check first incase there are delayed event that cleanBMap may remove.
    where
    check [] = []
    -- All known values of Just anything must be at a Time (i.e. not JustAfter or Infintiy)
    check ((t, Just (Just _)) : _)
        | not (isExactlyDI t)
        = error $ "cleanEMapErr: found event on non Exactly time: " ++ errMsg
    -- All known values of Just anything must be instantaneous i.e. be
    -- followed immediately (DI_JustAfter) by a unknown or a known Nothing.
    check ((t1,x1) : (_, Just (Just _)) : _)
        | not (isJustAfterDI t1 && (case x1 of
                                        Nothing -> True
                                        Just Nothing -> True
                                        Just (Just _) -> False))
        = error $ "cleanEMapErr: found non-instantenous event occurence: " ++ errMsg
    check (_:xs) = check xs

-- | Knowlage of one event occurence.
-- knowlage: exactly t and no other time.
instantaneousEMap :: Time -> Maybe a -> EMap a
instantaneousEMap t aMay = EMap (instantaneousBMap t aMay)

-- | A sigle time span of knowlage with any number of events.
spanEMap
    :: Maybe TimeDI
    -- ^ When knowlage starts (Nothing means start on event occurence). If both
    -- this is Nothing, and there are no event occurences, then a null EMap is
    -- returned.
    -> [(Time, a)]
    -- ^ Event occurences. Must be in strictly increasing chronological order.
    -> Maybe TimeDI
    -- ^ When knowlage ends EXCLUSIVE! You'll likely want to use DI_JustAfter
    -- (Nothing means Infinity).
    -> EMap a
spanEMap Nothing [] _ = EMap (BMap [])
spanEMap knowlageStartTimeMay events knowlageEndTimeMay = cleanEMapErr "spanEMap" $ concat
        [ [(knowlageEndTime, Nothing) | Just knowlageEndTime <- [knowlageEndTimeMay]]
        , concat
            [ [ (DI_JustAfter eventTime, Just Nothing)
              , (DI_Exactly eventTime, Just (Just eventValue))
              ]
            | (eventTime, eventValue) <- events
            ]
        , [(knowlageStartTime, Just Nothing) | Just knowlageStartTime <- [knowlageStartTimeMay]]
        ]

-- | You'll likely want to add an initial value at time 0 after applying this
-- step. Not that after any period of know knowlage, we can no longer ensure
-- knowlage at the start of the next known time span because we may have missed
-- some events from the unknow time span.
stepEMap :: EMap a -> BMap a
stepEMap (EMap (BMap allXs)) = cleanBMapErr "stepEMap" $ go allXs
    -- TODO I'm not sure if `cleanBMapErr` is actually necessary. If you want to
    -- check, note that there are only 2 cases I clean here: Nothing at the end
    -- and consecutinve Nothings Note that since we never change or add times,
    -- we dont need to check that t(i) > t(i+1)

    where
    go [] = []
    go [(_,Nothing)] = error "stepEMap: Impossible! Event Invariant is that list doesn't end in Nothing"
    -- A single event, but we don't know "the last value", so we don't have
    -- knowlage here.
    go [(_,Just Nothing)] = []
    -- Since we have knowlage to infinity, and there is only this one event, we
    -- hold that value to infinty.
    go [(t,Just (Just a))] = [(t, Just a)]

    go ((t, Nothing) : xs) = (t, Nothing) : go xs
    -- Even though we have knowlage, since we
    go ((t1, Just Nothing) : (t2, Nothing) : xs)
        -- Since events occur on DI_exactly times, it is impossible for events
        -- to occur in such instantaneous unknow time spans.
        | t1 == delayTime t2    = go xs
        -- .. But all other unknown time spans mean that we may have missed some
        -- events, so we cant yet claim knowlage.
        | otherwise             = (t2, Nothing) : go xs
    go ((_, Just Nothing) : (_, Just Nothing) : _) = error "stepEMap: Impossible! Event Invariant is that list doesnt cave consecuting (Just Nothing)"
    -- The crux of what step does! Hold the event value of the most recent event.
    go ((_, Just Nothing) : (t2, Just (Just a)) : xs) = (t2, Just a) : go xs
    go ((t, Just (Just a)) : xs) = (t, Just a) : go xs


-- | Used to defined event step without exposing ability to delay events.
delayStepEMapWithExtra
    :: EMap a
    -- ^ This part will be delayed. We justify delaying an event (which you
    -- should never do!) because it's only a step in converting it into a
    -- behavior.
    -> EMap a
    -- ^ This part will not be delayed
    -> BMap a
    -- ^ Union of the above 2 (first delayed) and stepped.
delayStepEMapWithExtra emapA emapB  = let
    emapA' = EMap (delayTime (emapToBMap emapA))
    emap = gateUnion emapA' emapB
    in  stepEMap emap

sampleEMap :: forall a b c . (a -> b -> c) -> BMap a -> EMap b -> EMap c
sampleEMap f bmap emap = cleanEMapErr "sampleEMap" $ unBMap $ zipBMap zipper bmap (emapToBMap emap)
    -- ^ TODO I think this does cleanBMap twice :-(
    where
    zipper :: Maybe a -> Maybe (Maybe b) -> Maybe (Maybe c)
    zipper (Just a) (Just (Just b)) = Just (Just (f a b))
    zipper _ _ = Nothing

-- -- | Zip emaps.
-- zipEMap
--     :: _
--     -> EMap a
--     -> EMap b
--     -> EMap c
-- zipEMap f emapA emapB = EMap $ zipBMap f (emapToBMap emapA) (emapToBMap emapB)