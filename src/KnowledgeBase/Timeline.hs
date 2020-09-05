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

-- | Timeline of facts for an Event/Behavor.
module KnowledgeBase.Timeline
    ( Timeline
    , TimelineE (..)
    , TimelineB (..)
    , TimelineBVal (..)
    , MultiTimeline (..)

    , FactSpan (..)

    , VFact' (..)
    , FactB
    , FactBVal
    , FactE
    , MaybeChange (..)
    , NoChange (..)
    , NoChangeVal (..)
    , IsChange (..)
    , CropView (..)

    , empty
    , mtEmpty
    , toFactSpan
    , factSpanMinT
    , factSpanJustBeforeMinT
    -- , LookupIntersectingE (..)
    , tlLookup
    , tlNull
    , leftNeighbors
    , rightNeighbors
    -- , tUnion
    , mtUnion
    , mtFromList
    -- , lookupIntersecting
    -- , lookupIntersectingBVal
    -- , lookupIntersectingBOf
    , lookupIntersecting
    , mtLookupIntersecting
    , viewIntersecting
    , mtViewIntersecting
    , mtCropView
    -- , viewIntersectingBVal
    -- , viewIntersectingBOf
    , insertFact
    , setValueForallFactB
    , factBValToVal
    , factBToMayVal
    , factEToOcc
    ) where

import           Control.Monad (guard)
import           Data.List (foldl')
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Maybe (isJust, maybeToList)
import qualified Data.Set as Set
import           Data.Void
import           Data.Text.Prettyprint.Doc


import Time
import TimeSpan


--
-- VFact Span
--

-- Spans of time that can cover a single fact
data FactSpan
    = FS_Init
    -- ^ Just (Behavior) initial value
    | FS_Point Time
    -- ^ single point in time
    | FS_Span SpanExc
    -- ^ Span of time. `allT` does NOT include the (Behavior) initial value.
    deriving stock (Eq, Show)


instance Contains FactSpan Time where
    contains f t = case f of
        FS_Init -> False
        FS_Point t' -> t == t'
        FS_Span tspan -> tspan `contains` t
instance Contains FactSpan TimeX where
    contains f t = case f of
        FS_Init -> t == X_NegInf
        FS_Point t' -> t == toTime t'
        FS_Span tspan -> tspan `contains` t

instance Intersect FactSpan SpanExc (Maybe FactSpan) where
    intersect = flip intersect
instance Intersect SpanExc FactSpan (Maybe FactSpan) where
    intersect tspan fspan = case fspan of
        FS_Init -> Nothing
        FS_Point t -> if t `intersects` tspan then Just fspan else Nothing
        FS_Span tspan' -> FS_Span <$> intersect tspan tspan'

instance Intersect FactSpan Time (Maybe Time) where
    intersect = flip intersect
instance Intersect Time FactSpan (Maybe Time) where
    intersect t fspan = case fspan of
        FS_Init -> Nothing
        FS_Point t' -> if t == t' then Just t else Nothing
        FS_Span tspan -> if tspan `contains` t then Just t else Nothing

instance Intersect FactSpan FactSpan (Maybe FactSpan) where
    intersect FS_Init FS_Init = Just FS_Init
    intersect (FS_Point t) (FS_Point t')
        | t == t' = Just (FS_Point t)
    intersect (FS_Point t) (FS_Span tspan)
        | tspan `contains` t = Just (FS_Point t)
    intersect (FS_Span tspan) (FS_Point t)
        | tspan `contains` t = Just (FS_Point t)
    intersect (FS_Span tspan) (FS_Span tspan') = FS_Span <$> tspan `intersect` tspan'
    intersect _ _ = Nothing

instance Difference FactSpan FactSpan [FactSpan] where
    difference FS_Init FS_Init = []
    difference FS_Init _ = [FS_Init]

    difference a@(FS_Point _) FS_Init = [a]
    difference a@(FS_Point p) (FS_Point p')
        | p == p' = []
        | otherwise = [a]
    difference a@(FS_Point p) (FS_Span tspan)
        | tspan `contains` p = []
        | otherwise = [a]

    difference a@(FS_Span _) FS_Init = [a]
    difference a@(FS_Span tspan) (FS_Point t) = case splitSpanExcAt tspan t of
        FullyLeftOfT _ -> [a]
        FullyRightOfT _ -> [a]
        SplitByT l r ->[FS_Span l, FS_Span r]
    difference (FS_Span tspan) (FS_Span tspan') = let
        (lMay, rMay) = tspan `difference` tspan'
        in (maybe [] (\(s,t) -> [FS_Span s, FS_Point t])  lMay)
            ++ (maybe [] (\(t,s) -> [FS_Span s, FS_Point t])  rMay)

instance Difference FactSpan [FactSpan] [FactSpan] where
    difference a bs = go [a] bs
        where
        go xs [] = xs
        go xs (y:ys) = go (concatMap (`difference` y) xs) ys

-- | Nothing means Init
factSpanMinT :: FactSpan -> Maybe TimeX
factSpanMinT fs = case fs of
    FS_Init -> Nothing
    FS_Point t -> Just (X_Exactly t)
    FS_Span tspan -> Just (spanExcMinT tspan)

-- | Nothing means Init
factSpanMaxT :: FactSpan -> Maybe TimeX
factSpanMaxT fs = case fs of
    FS_Init -> Nothing
    FS_Point t -> Just (X_Exactly t)
    FS_Span tspan -> Just (spanExcMaxT tspan)

-- | Nothing means Init or just before a span starting at NegInf
factSpanJustBeforeMinT :: FactSpan -> Maybe TimeX
factSpanJustBeforeMinT fs = case fs of
    FS_Init -> Nothing
    FS_Point t -> Just (X_JustBefore t)
    FS_Span tspan -> toTime <$> spanExcJustBefore tspan

--
-- VFact
--

data VFact' initT pointT spanT
    = Init initT
    | ChangePoint Time pointT
    | ChangeSpan SpanExc spanT
    deriving (Show)

type FactB     a = VFact' a (MaybeChange a) NoChange
type FactBVal  a = VFact' a a (NoChangeVal a)
type FactE     a = VFact' Void (Maybe a) NoChange

newtype MaybeChange a = MaybeChange { unMaybeChange :: Maybe a }
data NoChange = NoChange
    deriving (Show)
newtype NoChangeVal a = NoChangeVal a -- ^ a value that hasn't changed from the previous time/fact
    deriving (Show)

-- | Does a fact indicate a change in value?
class IsChange a where
    isChange :: a -> Bool
    isChange = not . isNoChange
    isNoChange :: a -> Bool
    isNoChange = not . isChange
instance (IsChange pd, IsChange sd) => IsChange (VFact' id pd sd) where
    isChange (Init _) = True
    isChange (ChangePoint _ f) = isChange f
    isChange (ChangeSpan _ f) = isChange f
instance IsChange (MaybeChange a) where
    isChange = isJust . unMaybeChange
instance IsChange (NoChangeVal a) where
    isChange _ = False
instance IsChange NoChange where
    isChange _ = False

toFactSpan :: VFact' a b c -> FactSpan
toFactSpan (Init _) = FS_Init
toFactSpan (ChangePoint t _) = FS_Point t
toFactSpan (ChangeSpan tspan _) = FS_Span tspan

-- Replace all facts with the given value.
setValueForallFactB :: a -> FactB a -> FactBVal a
setValueForallFactB a (Init _) = Init a
setValueForallFactB a (ChangePoint t _) = ChangePoint t a
setValueForallFactB a (ChangeSpan tspan _) = ChangeSpan tspan (NoChangeVal a)

factBValToVal :: FactBVal a -> a
factBValToVal f = case f of
    Init a -> a
    ChangePoint _ a -> a
    ChangeSpan _ (NoChangeVal a) -> a

factBToMayVal :: FactB a -> Maybe a
factBToMayVal factB = case factB of
    Init a -> Just a
    ChangePoint _ (MaybeChange aMay) -> aMay
    ChangeSpan _ _ -> Nothing

factEToOcc :: FactE a -> Maybe a
factEToOcc factE = case factE of
    Init _ -> error "Impossible! found an event with an initial value."
    ChangePoint _ occMay -> occMay
    ChangeSpan _ _ -> Nothing

--
-- Timeline
--

data Timeline initT pointT spanT = Timeline (Maybe initT) (Map TimeX (VFact' initT pointT spanT))
    deriving (Show)
newtype TimelineB     a = TimelineB    { unTimelineB    :: Timeline a    (MaybeChange a) NoChange        }
newtype TimelineBVal  a = TimelineBVal { unTimelineBVal :: Timeline a    a               (NoChangeVal a) }
newtype TimelineE     a = TimelineE    { unTimelineE    :: Timeline Void (Maybe a)       NoChange        }

timelineFactSpans :: Timeline initT pointT spanT -> [FactSpan]
timelineFactSpans (Timeline initMay m)
    = [ FS_Init | Just _ <- [initMay] ]
    ++ (toFactSpan <$> Map.elems m)

timelineFactSpansB :: Timeline initT (MaybeChange pointT) NoChange -> [(FactSpan, IsOcc)]
timelineFactSpansB (Timeline initMay m)
    = [ (FS_Init, IsOcc) | Just _ <- [initMay] ]
    ++ [(toFactSpan f, case f of
            Init _ -> IsOcc
            ChangePoint _ (MaybeChange (Just _)) -> IsOcc
            ChangePoint _ (MaybeChange Nothing) -> IsNotOcc
            ChangeSpan _ NoChange -> IsNotOcc
        )
        | f <- Map.elems m]

timelineFactSpansE :: Timeline Void (Maybe pointT) NoChange -> [(FactSpan, IsOcc)]
timelineFactSpansE (Timeline _ m) = toFactSpanIsOcc <$> Map.elems m
    where
    toFactSpanIsOcc :: VFact' Void (Maybe pointT) NoChange -> (FactSpan, IsOcc)
    toFactSpanIsOcc (Init _) = (FS_Init, IsNotOcc)
    toFactSpanIsOcc (ChangePoint t (Just _)) = (FS_Point t, IsOcc)
    toFactSpanIsOcc (ChangePoint t Nothing) = (FS_Point t, IsNotOcc)
    toFactSpanIsOcc (ChangeSpan tspan _) = (FS_Span tspan, IsNotOcc)

data IsOcc = IsOcc | IsNotOcc
    deriving (Show)

-- | An empty Timeline
empty :: Timeline initT pointT spanT
empty = Timeline Nothing Map.empty

-- | An empty MultiTimeline
mtEmpty :: MultiTimeline a
mtEmpty = MultiTimeline []

-- | Lookup the fact at (i.e. intersecting) a TimeX.
tlLookup :: TimeX -> Timeline initT pointT spanT -> Maybe (VFact' initT pointT spanT)
tlLookup tx (Timeline initAMay m) = case tx of
    X_NegInf -> Init <$> initAMay
    _ -> do
        (_, candidateFact) <- Map.lookupLE tx m
        guard (toFactSpan candidateFact `contains` tx)
        return candidateFact

tlNull :: Timeline initT pointT spanT -> Bool
tlNull (Timeline Nothing m) = Map.null m
tlNull _ = False

-- TODO PREFORMANCE this should probably become some sort of BSP tree
-- Timeline with overlapping FactSpans
-- Map ix is lo time inclusive then hi time inclusive
newtype MultiTimeline a = MultiTimeline { unMultiTimeline :: [a] } -- arbitrary order order

insertFact :: VFact' id pd sd -> Timeline id pd sd -> Timeline id pd sd
insertFact f timelineB@(Timeline initAMay factMap)
    | not $ null $ lookupIntersecting timelineB $ toFactSpan f
        = error "insertFactB: overlapping fact."
    | otherwise = case f of
        Init a -> Timeline (Just a) factMap
        ChangePoint t _ -> Timeline initAMay (Map.insert (toTime t) f factMap)
        ChangeSpan tspan _ -> Timeline initAMay (Map.insert (spanExcMinT tspan) f factMap)

lookupIntersecting :: Timeline id pd sd -> FactSpan -> [VFact' id pd sd]
lookupIntersecting timeline factSpan = fst (viewIntersecting timeline factSpan)

viewIntersecting :: Timeline id pd sd -> FactSpan -> ([VFact' id pd sd], Timeline id pd sd)
viewIntersecting (Timeline initAMay m) factSpan = case factSpan of
    FS_Init -> ([Init a | Just a <- [initAMay]], Timeline Nothing m)
    _ -> let
        (tspanLo, intersectsFact) = case factSpan of
            FS_Init -> error "Impossible!"
            FS_Point t -> (X_Exactly t, intersects t)
            FS_Span tspan -> (spanExcMinT tspan, intersects tspan)
        prevFact = [ (k, f)
                | Just (k, f) <- [Map.lookupLT tspanLo m]
                , intersectsFact (toFactSpan f)
                ]
        rightFacts
            = takeWhile (\(_,f) -> intersectsFact (toFactSpan f))
            $ Map.assocs
            $ Map.dropWhileAntitone (< tspanLo) m
        intersectingFacts = prevFact ++ rightFacts
        m' = m `Map.withoutKeys` (Set.fromAscList (fst <$> intersectingFacts))
        in ( snd <$> intersectingFacts
            , Timeline initAMay m'
            )

mtLookupIntersecting :: (a -> FactSpan) -> MultiTimeline a -> FactSpan -> [a]
mtLookupIntersecting aToFactSpan (MultiTimeline allAs) factSpan
    = filter (intersects factSpan . aToFactSpan) allAs

mtViewIntersecting
    :: (a -> ([a], [a]))
    -- ^ View of a cropped by span. Returns (as in the span, as out of the span)
    -> MultiTimeline a
    -> ([a], MultiTimeline a)
    -- ^ (a's in the span, timeline with only the a's out side of the span)
mtViewIntersecting viewA (MultiTimeline allAs) = MultiTimeline <$> go allAs
    where
    go [] = ([], [])
    go (a:as) = viewA a <> go as

-- | Get all right neighbors starting just after the end of the given FactSpan.
rightNeighbors :: forall id pd sd
    .  Timeline id pd sd
    -> FactSpan
    -- ^ Current fact span. First neighbor start is just after the start of this fact span.
    -> [VFact' id pd sd]
rightNeighbors kBFactsB@(Timeline _ m) currFactSpan = case nextFactMay of
    Nothing -> []
    Just nextFact -> nextFact : rightNeighbors kBFactsB (toFactSpan nextFact)
    where
    nextFactMay :: Maybe (VFact' id pd sd)
    nextFactMay = case currFactSpan of
        FS_Init -> Map.lookup X_NegInf m
        FS_Point t
            -> Map.lookup (X_JustAfter t) m
        FS_Span tspan
            -> do
                -- If spanExcJustAfter gives Nothing then we've reached the
                -- end of time, so can stop.
                nextTx <- spanExcJustAfter tspan
                Map.lookup (X_Exactly nextTx) m
leftNeighbors :: forall id pd sd
    .  Timeline id pd sd
    -> FactSpan
    -- ^ Current fact span. First neighbor end is just before the start of this fact span.
    -> [VFact' id pd sd]
leftNeighbors timeline@(Timeline initA m) currFactSpan = case prevCFactMay of
    Nothing -> []
    Just prevCFact -> prevCFact : leftNeighbors timeline (toFactSpan prevCFact)
    where
    prevCFactMay :: Maybe (VFact' id pd sd)
    prevCFactMay = case currFactSpan of
        FS_Init -> Nothing
        FS_Point t
            -> do
                (_, prev) <- Map.lookupLT (X_Exactly t) m
                guard $ toFactSpan prev `isLeftNeighborOf` currFactSpan
                return prev
        FS_Span tspan
            -> case spanExcJustBefore tspan of
                Nothing -> Init <$> initA
                Just prevT -> do
                    (_, prev) <- Map.lookupLE (X_Exactly prevT) m
                    guard $ toFactSpan prev `isLeftNeighborOf` currFactSpan
                    return prev

{-}
lookupBValJustBefore :: FactSpan -> TimelineBVal a -> Maybe a
lookupBValJustBefore = _ -- leftNeighbors
-}

isLeftNeighborOf :: FactSpan -> FactSpan -> Bool
isLeftNeighborOf left right = factSpanMaxT left == factSpanJustBeforeMinT right

-- -- | Return true if the first span is to the left of the second (no overlap).
-- isLeftOf :: FactSpan -> FactSpan -> Bool
-- isLeftOf l r = case (factSpanMaxT l, factSnapMinT r) of

mtFromList :: [a] -> MultiTimeline a
mtFromList = MultiTimeline

mtUnion :: MultiTimeline a -> MultiTimeline a -> MultiTimeline a
mtUnion (MultiTimeline as) (MultiTimeline bs) = MultiTimeline (as ++ bs)

-- tUnion :: Timeline initT pointT spanT -> Timeline initT pointT spanT -> Timeline initT pointT spanT
-- tUnion = _

--
-- Crop i.e. removing exactly a span of time from the timeline
--

-- | This is basically a combination of Intersection (inside) and Difference (outside)
class CropView a span inside outside | a span -> inside, a span -> outside where
    -- | returns (the subset of a spanning the span, the subset of a outside the span)
    cropView :: a -> span -> (inside, outside)
    crop :: a -> span -> inside
    crop a s = fst (cropView a s)

mtCropView :: CropView a FactSpan [a] [a] => MultiTimeline a -> FactSpan -> (MultiTimeline a, MultiTimeline a)
mtCropView (MultiTimeline as) factSpan = (MultiTimeline ins, MultiTimeline outs)
    where
    (ins, outs) = mconcat
        [ cropView a factSpan
        | a <- as
        ]

instance ShiftFactSpanIntersecting (VFact' initT pointT spanT)
  => CropView (VFact' initT pointT spanT) FactSpan (Maybe (VFact' initT pointT spanT)) [VFact' initT pointT spanT] where
    cropView f cropSpan = let
        fSpan = toFactSpan f
        outsideSpans = cropSpan `difference` fSpan
        in if fSpan `intersects` cropSpan
            then (Just (shiftFactSpanIntersecting f cropSpan), shiftFactSpanIntersecting f <$> outsideSpans)
            else (Nothing, [f])
instance ShiftFactSpanIntersecting (VFact' initT pointT spanT)
  => CropView (Timeline initT pointT spanT) FactSpan [VFact' initT pointT spanT] (Timeline initT pointT spanT) where
    cropView timeline factSpan = let
        -- Initial pass just extractts overlapping facts (without breaking them down)
        (intersectingFacts, timelineOut') = viewIntersecting timeline factSpan
        -- Break facts into inside and outside.
        (insideFacts, outsideFacts) = mconcat
            [ (maybeToList mayIn, outs)
            | f <- intersectingFacts
            , let (mayIn, outs) = cropView f factSpan
            ]
        in (insideFacts, foldl' (flip insertFact) timelineOut' outsideFacts)

-- | Change the Span of a fact. Assumes the new and old time spans interesect.
-- This is to avoid converting to initT from pointT/spanT.
class ShiftFactSpanIntersecting fact where
    shiftFactSpanIntersecting :: fact -> FactSpan -> fact
instance ShiftFactSpanIntersecting (FactB a) where
    shiftFactSpanIntersecting f fs = case f of
        Init _ -> case fs of
            FS_Init -> f
            _ -> err
        ChangePoint t _ -> case fs of
            FS_Point t'
                | t == t'
                -> f
            _ -> err
        ChangeSpan tspan NoChange -> case fs of
            FS_Point t
                | tspan `contains` t
                -> ChangePoint t (MaybeChange Nothing)
            FS_Span tspan'
                | tspan `intersects` tspan'
                -> ChangeSpan tspan' NoChange
            _ -> err
        where
        err = error "shiftFactSpanIntersecting: expected intersecting fact and factspan"

instance ShiftFactSpanIntersecting (FactE a) where
    shiftFactSpanIntersecting f fs = case f of
        Init _ -> case fs of
            FS_Init -> f
            _ -> err
        ChangePoint t _ -> case fs of
            FS_Point t'
                | t == t'
                -> f
            _ -> err
        ChangeSpan tspan NoChange -> case fs of
            FS_Point t
                | tspan `contains` t
                -> ChangePoint t Nothing
            FS_Span tspan'
                | tspan `intersects` tspan'
                -> ChangeSpan tspan' NoChange
            _ -> err
        where
        err = error "shiftFactSpanIntersecting: expected intersecting fact and factspan"


instance Pretty FactSpan where
    pretty = viaShow
instance Pretty IsOcc where
    pretty = viaShow
instance Pretty (Timeline it pt st) where
    pretty timeline = "Timeline" <+> pretty (timelineFactSpans timeline)
instance Pretty (TimelineE a) where
    pretty timelineE = "Timeline" <+> pretty (timelineFactSpansE (unTimelineE timelineE))
instance Pretty (TimelineB a) where
    pretty timelineB = "Timeline" <+> pretty (timelineFactSpansB  (unTimelineB timelineB))
