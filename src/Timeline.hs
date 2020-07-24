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
import Data.List (foldl')
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Maybe (maybeToList)

import Time
import TimeSpan

--
-- I'm adapting http://groups.csail.mit.edu/mac/users/adams/BB/ such that index
-- is possibly a span rather than just a point.
--

-- | A timeline is a map from time to value where values may be set on spans of
-- time.
data Timeline a = Timeline
    (Map (Maybe Time) (Maybe Time, a))
    -- ^ Map from low time to high time and value (corresponds to DS_SpanExc).
    (Map Time a)
    -- ^ Map from time to value (corresponds to DS_Point).

empty :: Timeline a
empty = Timeline M.empty M.empty

null :: Timeline a -> Bool
null (Timeline m n) = M.null m && M.null n

singleton :: TimeSpan -> a -> Timeline a
singleton tts a = insert tts a empty

fromList :: [(TimeSpan, a)] -> Timeline a
fromList = foldl' (\tl (timeSpan, value) -> insert timeSpan value tl) empty

insert :: TimeSpan -> a -> Timeline a -> Timeline a
insert tts a (Timeline m n) = case tts of
    DS_Point t -> Timeline m (M.insert t a n)
    DS_SpanExc ts -> Timeline (M.insert (spanExcJustBefore ts) (spanExcJustAfter ts, a) m) n

-- | All elements in chronological order
elems :: Timeline a -> [(TimeSpan, a)]
elems (Timeline m n) = merge psTop ssTop
    where
    psTop = M.toAscList n
    ssTop = M.toAscList m

    merge [] ss = (\(lo, (hi, a)) -> (DS_SpanExc (spanExc lo hi), a)) <$> ss
    merge ps [] = (\(t, a) -> (DS_Point t, a)) <$> ps
    merge psAll@((p,ap):ps) ssAll@((lo,(hi,as)):ss) = case lo of
        Nothing -> pickS
        Just tLo
            | tLo < p   -> pickS
            | otherwise -> (DS_Point p, ap) : merge ps ssAll
        where
        pickS = (DS_SpanExc (spanExc lo hi), as) : merge psAll ss

-- | All elements in reverse chronological order
elemsRev :: Timeline a -> [(TimeSpan, a)]
elemsRev (Timeline m n) =merge psTop ssTop
    where
    psTop = M.toDescList n
    ssTop = M.toDescList m

    merge [] ss = (\(lo, (hi, a)) -> (DS_SpanExc (spanExc lo hi), a)) <$> ss
    merge ps [] = (\(t, a) -> (DS_Point t, a)) <$> ps
    merge psAll@((p,ap):ps) ssAll@((lo,(hi,as)):ss) = case hi of
        Nothing -> pickS
        Just tHi
            | tHi > p   -> pickS
            | otherwise -> (DS_Point p, ap) : merge ps ssAll
        where
        pickS = (DS_SpanExc (spanExc lo hi), as) : merge psAll ss

-- | Timeline contain keys that contain a time less than the give Time (spans are not cropped).
selectLT :: Time -> Timeline a -> Timeline a
selectLT t = select (Span Open (ClosedExc t))

-- | Elements in reverse chronological order that contain a time less than the give Time (spans are not cropped).
elemsLT :: Time -> Timeline a -> [(TimeSpan, a)]
elemsLT t = elemsRev . selectLT t

-- | Timeline contain keys that contain a time greater than the give Time (spans are not cropped).
selectGT :: Time -> Timeline a -> Timeline a
selectGT t = select (Span (ClosedExc t) Open)

-- | Elements in chronological order that contain the time just after the give Time.
elemsGT :: Time -> Timeline a -> [(TimeSpan, a)]
elemsGT t = elems . selectGT t

select :: Span -> Timeline a -> Timeline a
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
                Just (lo, v@(hi, _)) -> case hi of
                    Nothing -> withMarginEl
                    Just t' | tLo < t'  -> withMarginEl
                            | otherwise -> bs
                    where
                    withMarginEl = M.insert lo v bs

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

crop :: Span -> Timeline a -> Timeline a
crop sp@(Span loBound hiBound) tl = Timeline m' n'
    where
    -- Select
    Timeline sm sn = select sp tl

    -- Crop the first and last elements if needed
    (m_loBound, n_loBound) = case M.minViewWithKey sm of
        -- No min (implying empty)
        Nothing -> (sm, sn)
        Just ((lo', (hi', v)), mWithoutMin) -> case loBound of
            ClosedInc lo
                | Just lo > lo'
                -> ( insertErr (Just lo) (hi', v) mWithoutMin
                    , insertErr lo v sn
                    )
            ClosedExc lo
                | Just lo > lo'
                -> ( insertErr (Just lo) (hi', v) mWithoutMin
                    , sn
                    )
            _ -> (sm, sn)

    (m', n') = case M.maxViewWithKey m_loBound of
        -- No max (implying empty)
        Nothing -> (m_loBound, n_loBound)
        Just ((lo', (hi', v)), mWithoutMin) -> case hiBound of
            ClosedInc hi
                | maybe True (hi <) hi'
                -> ( insertErr lo' (hi', v) mWithoutMin
                   , insertErr hi v n_loBound
                   )
            ClosedExc hi
                | maybe True (hi <) hi'
                -> ( insertErr lo' (hi', v) mWithoutMin
                   , n_loBound
                   )
            _ -> (m_loBound, n_loBound)

    insertErr :: Ord k => k -> v -> Map k v -> Map k v
    insertErr = M.insertWith (\_ _ -> error "crop: Duplicate keys")


cropTimeSpan :: forall a . TimeSpan -> Timeline a -> Timeline a
cropTimeSpan ts = crop (timeSpanToSpan ts)

lookup :: Time -> Timeline a -> Maybe a
lookup t = fmap snd . lookup' t

lookup' :: Time -> Timeline a -> Maybe (TimeSpan, a)
lookup' t (Timeline m n) = case M.lookup t n of
    Nothing -> case M.lookupLT (Just t) m of
        Nothing -> Nothing
        Just (lo, (hi, a)) -> let
            tspan = spanExc lo hi
            in if tspan `contains` t
                then Just (DS_SpanExc tspan, a)
                else Nothing
    Just a -> Just (DS_Point t, a)


-- | Lookup the value just after the given time
lookupJustBefore' :: Time -> Timeline a -> Maybe (TimeSpan, a)
lookupJustBefore' t tl = case elemsLT t tl of
    x@(ts,_):_
        | DS_SpanExc tss <- ts -- lookupJustBefore' can only return a DS_SpanExc fact.
        , spanExcJustAfter tss == Just t
        -> Just x
    _ -> Nothing

-- | Lookup the value just after the given time
lookupJustAfter' :: Time -> Timeline a -> Maybe (TimeSpan, a)
lookupJustAfter' t tl = case elemsGT t tl of
    x@(ts,_):_
        | DS_SpanExc tss <- ts -- lookupJustAfter' can only return a DS_SpanExc fact.
        , spanExcJustBefore tss == Just t
        -> Just x
    _ -> Nothing

-- Lookup the fact spanning negative infinity.
lookupNegInf' :: Timeline a -> Maybe (TimeSpan, a)
lookupNegInf' tl = case elems tl of
    x@(ts,_):_
        | DS_SpanExc tss <- ts
        , spanExcJustBefore tss == Nothing
        -> Just x
    _ -> Nothing

-- | Lookup the fact spanning the start of the given timespan.
lookupAtStartOf' :: TimeSpan -> Timeline a -> Maybe (TimeSpan, a)
lookupAtStartOf' tts tl = case tts of
    DS_Point t -> lookup' t tl
    DS_SpanExc ts -> case spanExcJustBefore ts of
        Nothing -> lookupNegInf' tl
        Just tLo -> lookupJustAfter' tLo tl

union :: forall a . Timeline a -> Timeline a -> Timeline a
union (Timeline ma na) (Timeline mb nb) = Timeline (ma <> mb) (na <> nb)

{-}

union :: forall a . Timeline a -> Timeline a -> Timeline a
union = error "TODO implement union"
    where
    -- See paper for hedge union. Note the paper includes specialized versions
    -- for open SpanBounds.

    -- | unbalanced filter only for elements in the given span.
    trim :: Span -> Timeline a -> Timeline a
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

    uni :: Span -> Timeline a -> Timeline a -> Timeline a
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

    concat3 :: TimeSpan -> a -> Timeline a -> Timeline a -> Timeline a
    concat3 = _

-- | Get only facts that intersect the time span. This also crops the facts that
-- span the edge of the time span.
cropTimeSpan :: forall a . TimeSpan -> Timeline a -> Timeline a
cropTimeSpan ts = cropList (timeSpanToSpan ts)
    where
    -- TODO I need a more general SpanExc that might include the lo/high points
    -- right now I'm using the union of the Maybe Time and SpanExc.
    cropList
        :: Span -- The space of possible keys in tl
        -> Timeline a
        -> Timeline a
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

timeSpanToSpan :: TimeSpan -> Span
timeSpanToSpan tts = case tts of
    DS_Point t -> Span (ClosedInc t) (ClosedInc t)
    DS_SpanExc ts -> spanExcToSpan ts

instance Semigroup (Timeline a) where
    (<>) = union

instance Monoid (Timeline a) where
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
data TimeSpan
    -- | DS_Point x ⟹ t < x
    = DS_Point Time
    -- | DS_SpanExc tspan ⟹ t ∈ tspan
    | DS_SpanExc SpanExc
    deriving (Show)

instance Intersect TimeSpan SpanExc (Maybe TimeSpan) where intersect = flip intersect
instance Intersect SpanExc TimeSpan (Maybe TimeSpan) where
    intersect t (DS_Point t')     = DS_Point   <$> intersect t t'
    intersect t (DS_SpanExc tspan)  = DS_SpanExc <$> intersect t tspan

instance Intersect Time TimeSpan (Maybe Time) where intersect = flip intersect
instance Intersect TimeSpan Time (Maybe Time) where
    intersect (DS_Point t)     t' = intersect t t'
    intersect (DS_SpanExc tspan) t  = intersect tspan t

instance Intersect TimeSpan TimeSpan (Maybe TimeSpan) where
    intersect (DS_Point t)     ds = DS_Point <$> intersect t ds
    intersect (DS_SpanExc tspan) ds = intersect tspan ds

instance Contains TimeSpan TimeSpan where
    contains (DS_Point a) (DS_Point b) = contains a b
    contains (DS_Point a) (DS_SpanExc b) = contains a b
    contains (DS_SpanExc a) (DS_Point b) = contains a b
    contains (DS_SpanExc a) (DS_SpanExc b) = contains a b

instance Contains SpanExc TimeSpan where
    contains a (DS_Point b) = contains a b
    contains a (DS_SpanExc b) = contains a b

instance Contains TimeSpan Time where
    contains (DS_Point t) t' = contains t t'
    contains (DS_SpanExc tspan) t = contains tspan t

instance Difference TimeSpan TimeSpan [TimeSpan] where
    difference (DS_Point a) (DS_Point b)
        | a == b = []
        | otherwise = [DS_Point a]
    difference (DS_Point a) (DS_SpanExc b) = fmap DS_Point . maybeToList $ a `difference` b
    difference (DS_SpanExc a) (DS_Point b) = DS_SpanExc <$> a `difference` b
    difference (DS_SpanExc a) (DS_SpanExc b) = concat
        [ l ++ r
        | let (x, y) = a `difference` b
        , let l = case x of
                Nothing -> []
                Just (tspan, t) -> [DS_SpanExc tspan, DS_Point t]
        , let r = case y of
                Nothing -> []
                Just (t, tspan) -> [DS_SpanExc tspan, DS_Point t]
        ]
instance Difference [TimeSpan] TimeSpan [TimeSpan] where
    difference a b = concatMap (`difference` b) a
instance Difference TimeSpan [TimeSpan] [TimeSpan] where
    difference a bs = foldl' difference [a] bs

{-}

--
-- Internal
--

timeline :: TimeSpan -> a -> Timeline a -> Timeline a -> Timeline a
timeline ts a l r = Timeline (size l + size r + 1) ts a l r

-- | In the paper, this is the rebalancing smart constructor T'
-- Must be from a balanced tree such that the one of the left or right tree may
-- have changed by at most 1 in size.
rebalanceTimeline :: TimeSpan -> a -> Timeline a -> Timeline a -> Timeline a
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

singleL :: TimeSpan -> a -> Timeline a -> Timeline a -> Timeline a
singleL ta a x (Timeline _ tb b y z) = timeline tb b (timeline ta a x y) z
singleL _ _ _ _ = undefined

doubleL :: TimeSpan -> a -> Timeline a -> Timeline a -> Timeline a
doubleL ta a x (Timeline _ tc c (Timeline _ tb b y1 y2) z)
    = timeline tb b (timeline ta a x y1) (timeline tc c y2 z)
doubleL _ _ _ _ = undefined

singleR :: TimeSpan -> a -> Timeline a -> Timeline a -> Timeline a
singleR tb b (Timeline _ ta a x y) z = timeline ta a x (timeline tb b y z)
singleR _ _ _ _ = undefined

doubleR :: TimeSpan -> a -> Timeline a -> Timeline a -> Timeline a
doubleR tc c (Timeline _ ta a x (Timeline _ tb b y1 y2)) z
    = timeline tb b (timeline ta a x y1) (timeline tc c y2 z)
doubleR _ _ _ _ = undefined
-}