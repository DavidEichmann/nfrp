{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wincomplete-uni-patterns #-}

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | Timeline of facts for a value.
module Timeline
    -- ( Timeline
    -- , empty
    -- , singleton
    -- , fromList
    -- , size
    -- , null
    -- , insert
    -- , cropTimeSpan
    -- , lookup
    -- , lookup'
    -- , lookupJustBefore'
    -- , lookupJustAfter'
    -- , lookupNegInf'
    -- , lookupAtStartOf'
    -- , elems
    -- , elemsGT
    -- , TimeSpan(..)
    -- )
     where

import Prelude hiding (lookup, null)
import Data.List (inits, tails, nub, foldl')
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Time
import TimeSpan
import Theory (MaybeOcc, pattern NoOcc, pattern Occ)
import GHC.Stack (HasCallStack)
import Control.Exception (assert)
import Data.Either (partitionEithers)
import Data.Maybe (isJust)

-- | A timeline is a map from time to value where values may be set on spans of
-- time.
data Timeline trace a = Timeline
    (Map (Maybe Time) (trace, Maybe Time))
    -- ^ Map from low time to high time of NoOcc value (corresponds to NoOcc DS_SpanExc).
    (Map Time (trace, MaybeOcc a))
    -- ^ Map from time to value (corresponds to a possible Occ at DS_Point).

empty :: Timeline trace a
empty = Timeline M.empty M.empty

null :: Timeline trace a -> Bool
null (Timeline m n) = M.null m && M.null n

singletonNoOcc :: trace -> TimeSpan -> Timeline trace a
singletonNoOcc tr tts = insertNoOcc tr tts empty

singletonOcc :: trace -> Time -> a -> Timeline trace a
singletonOcc tr t a = insertOcc tr t a empty

fromList :: [(trace, TimeSpan)] -> [(trace, Time, a)] -> Timeline trace a
fromList noOccs occs = foldl' (\tl (tr, timeSpan) -> insertNoOcc tr timeSpan tl) occsTl noOccs
    where
    occsTl = foldl' (\tl (tr, timeSpan, value) -> insertOcc tr timeSpan value tl) empty occs

insertNoOcc :: HasCallStack => trace -> TimeSpan -> Timeline trace a -> Timeline trace a
insertNoOcc tr tts tl@(Timeline m n) = assertTimeline $ case tts of
    DS_Point t
        | isJust (lookup t tl) -> error $ "insertNoOcc: key already exists at " ++ show tts
        | otherwise -> Timeline m (M.insert t (tr, NoOcc) n)
    DS_SpanExc ts
        | tl' <- select (spanExcToSpan ts) tl
        , not (null tl') -> error $ "insertNoOcc: existing keys " ++ show (keys tl') ++ " intersects new key " ++ show tts
        | otherwise -> Timeline (M.insert (spanExcJustBefore ts) (tr, spanExcJustAfter ts) m) n
insertOcc :: trace -> Time -> a -> Timeline trace a -> Timeline trace a
insertOcc tr t a (Timeline m n) = assertTimeline $ Timeline m (M.insert t (tr, Occ a) n)

keys :: Timeline trace a -> [Span]
keys tl = either timeSpanToSpan (timeToSpan . fst) . snd <$> elems tl

-- | All elements in chronological order
elems :: forall trace a . Timeline trace a -> [(trace, Either TimeSpan (Time, a))]
elems (Timeline m n) = merge psTop ssTop
    where
    psTop = M.toAscList n
    ssTop = M.toAscList m

    merge :: [(Time, (trace, MaybeOcc a))] -> [(Maybe Time, (trace, Maybe Time))] -> [(trace, Either TimeSpan (Time, a))]
    merge [] ss = (\(lo, (tr,hi)) -> (tr, Left (DS_SpanExc (spanExc lo hi)))) <$> ss
    merge ps [] = (\(t, (tr, aMay)) -> (tr, case aMay of
        NoOcc -> Left (DS_Point t)
        Occ a -> Right (t, a))) <$> ps
    merge psAll@((p,(ptr,ap)):ps) ssAll@((lo,(str,hi)):ss) = case lo of
        Nothing -> pickS
        Just tLo
            | tLo < p   -> pickS
            | otherwise -> (ptr, case ap of
                    NoOcc -> Left (DS_Point p)
                    Occ a -> Right (p, a)
                ) : merge ps ssAll
        where
        pickS = (str, Left (DS_SpanExc (spanExc lo hi))) : merge psAll ss

-- | All elements in reverse chronological order
elemsRev :: forall trace a . Timeline trace a -> [(trace, Either TimeSpan (Time, a))]
elemsRev (Timeline m n) = merge psTop ssTop
    where
    psTop = M.toDescList n
    ssTop = M.toDescList m

    merge :: [(Time, (trace, MaybeOcc a))] -> [(Maybe Time, (trace, Maybe Time))] -> [(trace, Either TimeSpan (Time, a))]
    merge [] ss = (\(lo, (tr,hi)) -> (tr, Left (DS_SpanExc (spanExc lo hi)))) <$> ss
    merge ps [] = (\(t, (tr, aMay)) -> (tr, case aMay of
        NoOcc -> Left (DS_Point t)
        Occ a -> Right (t, a))) <$> ps
    merge psAll@((p,(ptr,ap)):ps) ssAll@((lo,(str,hi)):ss) = case hi of
        Nothing -> pickS
        Just tHi
            | tHi > p   -> pickS
            | otherwise -> (ptr, case ap of
                    NoOcc -> Left (DS_Point p)
                    Occ a -> Right (p, a)
                ) : merge ps ssAll
        where
        pickS = (str, Left (DS_SpanExc (spanExc lo hi))) : merge psAll ss

-- | Timeline contain keys that contain a time less than the give Time (spans are not cropped).
selectLT :: Time -> Timeline trace a -> Timeline trace a
selectLT t = select (Span Open (ClosedExc t))

-- | Elements in reverse chronological order that contain a time less than the give Time (spans are not cropped).
elemsLT :: Time -> Timeline trace a -> [(trace, Either TimeSpan (Time, a))]
elemsLT t = elemsRev . selectLT t

-- | Timeline contain keys that contain a time greater than the give Time (spans are not cropped).
selectGT :: Time -> Timeline trace a -> Timeline trace a
selectGT t = select (Span (ClosedExc t) Open)

-- | Elements in chronological order that contain the time just after the give Time.
elemsGT :: Time -> Timeline trace a -> [(trace, Either TimeSpan (Time, a))]
elemsGT t = elems . selectGT t

select :: Span -> Timeline trace a -> Timeline trace a
select (Span loBound hiBound) (Timeline m n) = Timeline m' n'
    where
    -- Apply lower bound
    n_loBound = case loBound of
        Open -> n
        ClosedInc t -> M.dropWhileAntitone ( < t) n
        ClosedExc t -> M.dropWhileAntitone (<= t) n
    -- Apply upper bound
    n' =  case hiBound of
        Open -> n_loBound
        ClosedInc t -> M.takeWhileAntitone (<= t) n_loBound
        ClosedExc t -> M.takeWhileAntitone ( < t) n_loBound

    -- Apply lower bound
    m_loBound = case loBound of
        Open -> m
        ClosedInc tLo -> m_loBound' tLo
        ClosedExc tLo -> m_loBound' tLo
        where
        m_loBound' tLo = let
            (as, bs) = M.spanAntitone (\lo -> case lo of
                    Nothing -> True
                    Just t' -> t' < tLo
                ) m
            in case M.lookupMax as of
                Nothing -> bs
                Just (lo, (tr, hi)) -> case hi of
                    Nothing -> withMarginEl
                    Just t' | tLo < t'  -> withMarginEl
                            | otherwise -> bs
                    where
                    withMarginEl = M.insert lo (tr,hi) bs

    -- Apply upper bound
    m' =  case hiBound of
        Open -> m_loBound
        ClosedInc tHi -> m'' tHi
        ClosedExc tHi -> m'' tHi
        where
        m'' tHi = M.takeWhileAntitone (\loMay -> case loMay of
                    Nothing -> True
                    Just lo -> lo < tHi
                ) m_loBound

crop :: HasCallStack => Span -> Timeline trace a -> Timeline trace a
crop sp@(Span loBound hiBound) tl@(Timeline m n) = assertTimeline $ Timeline m' n'
    where
    -- Select
    Timeline sm sn = select sp tl

    -- Crop the first elements if needed
    (m_loBound, n_loBound) = case M.minViewWithKey sm of
        -- No min (implying empty)
        Nothing -> (sm, sn)
        Just ((lo', (tr, hi')), mWithoutMin) -> case loBound of
            ClosedInc lo
                | lo' < Just lo
                -> ( insertErr (spanExc lo' hi') (Just lo) (tr, hi') mWithoutMin
                    , insertErr (spanExc lo' hi') lo (tr, NoOcc) sn -- insert point since we include lo
                    )
            ClosedExc lo
                | lo' < Just lo
                -> ( insertErr (spanExc lo' hi') (Just lo) (tr, hi') mWithoutMin
                    , sn
                    )
            _ -> (sm, sn)

    -- Crop the last elements if needed
    (m', n') = case M.maxViewWithKey m_loBound of
        -- No max (implying empty)
        Nothing -> (m_loBound, n_loBound)
        Just ((lo', (tr, hi')), mWithoutMin) -> case hiBound of
            ClosedInc hi
                | maybe True (hi <) hi'
                -> ( insertErr (spanExc lo' hi') lo' (tr, hi') mWithoutMin
                   , insertErr (spanExc lo' hi') hi (tr, NoOcc) n_loBound -- insert point since we include hi
                   )
            ClosedExc hi
                | maybe True (hi <) hi'
                -> ( insertErr (spanExc lo' hi') lo' (tr, hi') mWithoutMin
                   , n_loBound
                   )
            _ -> (m_loBound, n_loBound)

    insertErr :: (HasCallStack, Ord k, Show k) => SpanExc -> k -> v -> Map k v -> Map k v
    insertErr derivedFrom = M.insertWithKey (\k _ _ -> error $ "crop: Duplicate keys at "
                                    ++ show k
                                    ++ " (derived from "
                                    ++ show derivedFrom
                                    ++ ") when cropping for "
                                    ++ show sp
                                    ++ ". n = " ++ show (M.keys n)
                                    ++ ". sn = " ++ show (M.keys sn)
                                )


cropTimeSpan :: forall a trace . HasCallStack => TimeSpan -> Timeline trace a -> Timeline trace a
cropTimeSpan ts = crop (timeSpanToSpan ts)

lookup :: Time -> Timeline trace a -> Maybe (MaybeOcc a)
lookup t = fmap (either (const NoOcc) id . snd) . lookup' t

lookup' :: Time -> Timeline trace a -> Maybe (trace, Either SpanExc (MaybeOcc a))
lookup' t (Timeline m n) = case M.lookup t n of
    Nothing -> case M.lookupLT (Just t) m of
        Nothing -> Nothing
        Just (lo, (tr, hi)) -> let
            tspan = spanExc lo hi
            in if tspan `contains` t
                then Just (tr, Left tspan)
                else Nothing
    Just (tr, a) -> Just (tr, Right a)


-- | Look for a NoOcc span just after the given time.
lookupJustBefore' :: Time -> Timeline trace a -> Maybe (trace, SpanExc)
lookupJustBefore' t tl = case elemsLT t tl of
    (tr, Left ts):_
        | DS_SpanExc tss <- ts -- lookupJustBefore' can only return a DS_SpanExc fact.
        , spanExcJustAfter tss == Just t
        -> Just (tr, tss)
    _ -> Nothing

-- | Lookup for a NoOcc span just after the given time.
lookupJustAfter' :: Time -> Timeline trace a -> Maybe (trace, SpanExc)
lookupJustAfter' t tl = case elemsGT t tl of
    (tr, Left ts):_
        | DS_SpanExc tss <- ts -- lookupJustAfter' can only return a DS_SpanExc fact.
        , spanExcJustBefore tss == Just t
        -> Just (tr, tss)
    _ -> Nothing

-- Lookup the NoOcc fact spanning negative infinity.
lookupNegInf' :: Timeline trace a -> Maybe (trace, SpanExc)
lookupNegInf' tl = case elems tl of
    (tr, Left ts):_
        | DS_SpanExc tss <- ts
        , spanExcJustBefore tss == Nothing
        -> Just (tr, tss)
    _ -> Nothing

-- | Lookup the fact equal to the point time or NoOcc fact spanning the start of
-- the SpanExc timespan.
lookupAtStartOf' :: TimeSpan -> Timeline trace a -> Maybe (trace, Either SpanExc (Time, MaybeOcc a))
lookupAtStartOf' tts tl = case tts of
    DS_Point t -> (fmap . fmap) (t,) <$> lookup' t tl
    DS_SpanExc ts -> fmap Left <$> case spanExcJustBefore ts of
        Nothing -> lookupNegInf' tl
        Just tLo -> lookupJustAfter' tLo tl

union :: forall trace a . HasCallStack => Timeline trace a -> Timeline trace a -> Timeline trace a
union (Timeline ma na) (Timeline mb nb) = assertTimeline $ Timeline (ma <> mb) (na <> nb)

{-}

union :: forall trace a . Timeline trace a -> Timeline trace a -> Timeline trace a
union = error "TODO implement union"
    where
    -- See paper for hedge union. Note the paper includes specialized versions
    -- for open SpanBounds.

    -- | unbalanced filter only for elements in the given span.
    trim :: Span -> Timeline trace a -> Timeline trace a
    trim _ Empty = Empty
    trim sp (Timeline _ ta a l r) = if _
        then if _
            then _
            else _
        else _
        where
        sp = timeSpanToSpan ta
        lSpace = beforeSpan sp
        rSpace = afterSpan sp

    uni :: Span -> Timeline trace a -> Timeline trace a -> Timeline trace a
    uni _ s Empty = s
    uni _ Empty (Timeline _ ta a l r) = concat3
    uni sp
        tl1@(Timeline _ ta1 a1 l1 r1)
        tl2@(Timeline _ ta2 a2 l2 r2)
        = concat3 ta1 a1
            (case lSpaceMay of
                Nothing -> Empty
                Just lSpace -> uni lSpace l1 (trim lSpace tl2)
            )
            (case rSpaceMay of
                Nothing -> Empty
                Just rSpace -> uni rSpace r1 (trim rSpace tl2)
            )
        where
        lSpaceMay = intersect sp =<< beforeSpan (timeSpanToSpan ta1)
        rSpaceMay = intersect sp =<< afterSpan (timeSpanToSpan ta1)

    concat3 :: TimeSpan -> a -> Timeline trace a -> Timeline trace a -> Timeline trace a
    concat3 = _

-- | Get only facts that intersect the time span. This also crops the facts that
-- span the edge of the time span.
cropTimeSpan :: forall a . TimeSpan -> Timeline trace a -> Timeline trace a
cropTimeSpan ts = cropList (timeSpanToSpan ts)
    where
    -- TODO I need a more general SpanExc that might include the lo/high points
    -- right now I'm using the union of the Maybe Time and SpanExc.
    cropList
        :: Span -- The space of possible keys in tl
        -> Timeline trace a
        -> Timeline trace a
    cropList space tl = case tl of
        Empty -> empty
        (Timeline _ ts' a l r) ->
            -- TODO if we transition to Span from SpanExc, we can use balancing
            -- constructor instead of union

            -- Current element
            (case sp''May of
                Nothing -> empty
                Just sp'' -> fromList [(ts'', a) | ts'' <- spanToTimeSpans sp'']
            )
            -- Left
            <> maybe empty (`cropList` l) lSpaceMay
            -- Right
            <> maybe empty (`cropList` r) rSpaceMay
            where
            sp' = timeSpanToSpan ts'
            sp''May = sp' `intersect` space
            lSpaceMay = intersect space =<< beforeSpan sp'
            rSpaceMay = intersect space =<< afterSpan sp'

spanToTimeSpans :: Span -> [TimeSpan]
spanToTimeSpans (Span l h) = case (l,h) of
    (Open, Open) -> [DS_SpanExc (spanExc Nothing Nothing)]
    (Open, ClosedExc b) -> [DS_SpanExc (spanExc Nothing (Just b))]
    (Open, ClosedInc b) -> [DS_SpanExc (spanExc Nothing (Just b)), DS_Point b]
    (ClosedExc a, Open) -> [DS_SpanExc (spanExc (Just a) Nothing)]
    (ClosedExc a, ClosedExc b) -> [DS_SpanExc (spanExc (Just a) (Just b))]
    (ClosedExc a, ClosedInc b) -> [DS_SpanExc (spanExc (Just a) (Just b)), DS_Point b]
    (ClosedInc a, Open) -> [DS_Point  a, DS_SpanExc (spanExc (Just a) Nothing)]
    (ClosedInc a, ClosedExc b) -> [DS_Point  a, DS_SpanExc (spanExc (Just a) (Just b))]
    (ClosedInc a, ClosedInc b) -> [DS_Point  a, DS_SpanExc (spanExc (Just a) (Just b)), DS_Point b]
-}

instance Semigroup (Timeline trace a) where
    (<>) = union

instance Monoid (Timeline trace a) where
    mempty = empty

{-}
data TimeVsTimeSpanOrdering
    = TTSO_Before
    | TTSO_During
    | TTSO_After

timeCompareTimeSpan :: Time -> TimeSpan -> TimeVsTimeSpanOrdering
timeCompareTimeSpan t ts = case ts of
    DS_Point t'
        | t < t'     -> TTSO_Before
        | t == t'    -> TTSO_During
        | otherwise  -> TTSO_After
    DS_SpanExc tse
        | tse `contains` t -> TTSO_During
        | Just lo <- spanExcJustBefore tse
        , t <= lo -> TTSO_Before
        | otherwise -> TTSO_After

data TimeSpanOrdering
    = TSO_LT
    | TSO_GT

timeSpanCompare :: TimeSpan -> TimeSpan -> Maybe TimeSpanOrdering
timeSpanCompare a' b' = case (a', b') of
    (DS_Point a, DS_Point b) -> case compare a b of
        LT -> Just TSO_LT
        GT -> Just TSO_GT
        EQ -> Nothing

    (DS_Point a, DS_SpanExc b)
        | Just bLo <- spanExcJustBefore b
        , a <= bLo
        -> Just TSO_LT

        | Just bHi <- spanExcJustAfter b
        , a >= bHi
        -> Just TSO_GT

    (DS_SpanExc _,  DS_Point _) -> timeSpanCompare b' a'

    (DS_SpanExc a,  DS_SpanExc b)
        | Just bLo <- spanExcJustBefore b
        , LeftSpaceExc bLo `contains` a
        -> Just TSO_LT

        | Just bHi <- spanExcJustAfter b
        , RightSpaceExc bHi `contains` a
        -> Just TSO_GT

    _ -> Nothing
-}

{-}

--
-- Internal
--

timeline :: TimeSpan -> a -> Timeline trace a -> Timeline trace a -> Timeline trace a
timeline ts a l r = Timeline (size l + size r + 1) ts a l r

-- | In the paper, this is the rebalancing smart constructor T'
-- Must be from a balanced tree such that the one of the left or right tree may
-- have changed by at most 1 in size.
rebalanceTimeline :: TimeSpan -> a -> Timeline trace a -> Timeline trace a -> Timeline trace a
rebalanceTimeline ts a l r
    = if ln + rn < 2
        then timeline ts a l r
        else if rn > weight * ln
            -- Right is too big.
            then let
                (rl, rr) = case r of
                    Timeline _ _ _ rl' rr' -> (rl', rr')
                    _ -> undefined
                rln = size rl
                rrn = size rr
                in if rln < rrn then singleL ts a l r else doubleL ts a l r
            else if ln > weight * rn
                -- Left is too big.
                then let
                    (ll, lr) = case l of
                        Timeline _ _ _ ll' lr' -> (ll', lr')
                        _ -> undefined
                    lln = size ll
                    lrn = size lr
                    in if lrn < lln then singleR ts a l r else doubleR ts a l r
                else timeline ts a l r
    where
    ln = size l
    rn = size r

    -- The paper goes into more detail about choosing a weight, but the quick
    -- version is "> 3.75" is necessary and a "integral value >= 4" is fine.
    weight = 4

-- Rotations

singleL :: TimeSpan -> a -> Timeline trace a -> Timeline trace a -> Timeline trace a
singleL ta a x (Timeline _ tb b y z) = timeline tb b (timeline ta a x y) z
singleL _ _ _ _ = undefined

doubleL :: TimeSpan -> a -> Timeline trace a -> Timeline trace a -> Timeline trace a
doubleL ta a x (Timeline _ tc c (Timeline _ tb b y1 y2) z)
    = timeline tb b (timeline ta a x y1) (timeline tc c y2 z)
doubleL _ _ _ _ = undefined

singleR :: TimeSpan -> a -> Timeline trace a -> Timeline trace a -> Timeline trace a
singleR tb b (Timeline _ ta a x y) z = timeline ta a x (timeline tb b y z)
singleR _ _ _ _ = undefined

doubleR :: TimeSpan -> a -> Timeline trace a -> Timeline trace a -> Timeline trace a
doubleR tc c (Timeline _ ta a x (Timeline _ tb b y1 y2)) z
    = timeline tb b (timeline ta a x y1) (timeline tc c y2 z)
doubleR _ _ _ _ = undefined
-}

assertTimeline :: HasCallStack => Timeline trace a -> Timeline trace a
assertTimeline tl = tl
-- assertTimeline tl = isValidTimeline tl

-- Returns errors
checkTimeline :: Timeline trace a -> [String]
checkTimeline tl
    -- No overlap of keys
    =
        [ "Overlapping keys (" ++ show a ++ ", " ++ show b ++ ")"
        | a:bs <- tails (keys tl)
        , b <- bs
        , a `intersects` b
        ]