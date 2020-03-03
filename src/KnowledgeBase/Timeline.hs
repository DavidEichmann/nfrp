{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wincomplete-uni-patterns #-}

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
    ( TimelineE
    , TimelineB
    , TimelineBVal

    , FactSpan
    , FactSpanE
    , FactSpanB

    , Fact (..)
    , FactB (..)
    , FactBC (..)
    , FactBVal (..)
    , FactBCVal (..)
    , FactE (..)

    , LookupIntersectingE (..)
    , lookupIntersectingB
    , lookupIntersectingBVal
    , lookupIntersectingBOf
    , viewIntersectingB
    , viewIntersectingBVal
    , viewIntersectingBOf
    , insertFactE
    , insertFactB
    , insertFactBVal
    ) where

import qualified Data.Map as Map
import Data.Map (Map)

import KnowledgeBase.Ix
import Time
import TimeSpan

-- Spans of time that can cover a single fact
data FactSpanE
    = FSE_Point Time
    | FSE_Span SpanExc
type FactSpanB = FactSpan
data FactSpan
    = FS_Init
    -- ^ Just (Behavior) initial value
    | FS_Point Time
    -- ^ single point in time
    | FS_Span SpanExc
    -- ^ Span of time. `allT` does NOT include the (Behavior) initial value.
    | FS_All
    -- ^ All time including the (Behavior) initial value.

newtype TimelineE    a = TimelineE              (Map TimeX (FactE     a))

data    TimelineB    a = TimelineB    (Maybe a) (Map TimeX (FactBC    a))
data    TimelineBVal a = TimelineBVal (Maybe a) (Map TimeX (FactBCVal a))
data    TimelineBOf init item
                       = TimelineTimelineBOf init (Map TimeX [item])

data Fact game
    = forall a . FactB (KeyB game a) (FactB a)
    | forall a . FactE (KeyE game a) (FactE a)

data FactB a
    = FB_Init a
    | FB_Change (FactBC a)

data FactBC a
    = FBC_Change Time (Maybe a)
    | FBC_NoChange SpanExc

data FactBVal a
    = FBV_InitVal a
    | FBV_Change (FactBCVal a)

data FactBCVal a
    = FBCV_Change Time a
    | FBCV_NoChange SpanExc a

data FactE a
    = FE_Occ Time a
    | FE_NoOcc SpanExc

-- | Removes the initial value if spanning it.
cropFactSpanBToE :: FactSpanB -> FactSpanE
cropFactSpanBToE = _

class ToFactSpanE fact where
    toFactSpanE :: fact -> FactSpanE
instance ToFactSpanE (FactE a) where
    toFactSpanE (FE_Occ t _) = FSE_Point t
    toFactSpanE (FE_NoOcc tspan) = FSE_Span tspan

class ToFactSpan fact where
    toFactSpan :: fact -> FactSpan
instance ToFactSpan (Fact a) where
    toFactSpan (FactB _ f) = toFactSpan f
    toFactSpan (FactE _ f) = toFactSpan f
instance ToFactSpan (FactBC a) where
    toFactSpan (FBC_Change t _) = FS_Point t
    toFactSpan (FBC_NoChange tspan) = FS_Span tspan
instance ToFactSpan (FactB a) where
    toFactSpan (FB_Init _) = FS_Init
    toFactSpan (FB_Change f) = toFactSpan f
instance ToFactSpan (FactBVal a) where
    toFactSpan (FBV_InitVal _) = FS_Init
    toFactSpan (FBV_Change f) = toFactSpan f
instance ToFactSpan (FactBCVal a) where
    toFactSpan (FBCV_Change t _) = FS_Point t
    toFactSpan (FBCV_NoChange tspan _) = FS_Span tspan
instance ToFactSpan (FactE a) where
    toFactSpan (FE_Occ t _) = FS_Point t
    toFactSpan (FE_NoOcc tspan) = FS_Span tspan
toFactSpanB :: ToFactSpan fact => fact -> FactSpanB
toFactSpanB = toFactSpan

insertFactB :: FactB a -> TimelineB a -> TimelineB a
insertFactB f timelineB@(TimelineB initAMay factMap)
    | not $ null $ lookupIntersectingB timelineB $ toFactSpan f
        = error "insertFactB: overlapping fact."
    | otherwise = case f of
        FB_Init a
                -> TimelineB (Just a) factMap
        FB_Change fbc@(FBC_Change t _)
                -> TimelineB initAMay (Map.insert (toTime t) fbc factMap)
        FB_Change fbc@(FBC_NoChange tspan)
                -> TimelineB initAMay (Map.insert (spanExcMinT tspan) fbc factMap)

insertFactBVal :: FactBVal a -> TimelineBVal a -> TimelineBVal a
insertFactBVal = _

insertFactE :: FactE a -> TimelineE a -> TimelineE a
insertFactE = _

lookupIntersectingB :: TimelineB a -> FactSpan -> [FactB a]
lookupIntersectingB timeline factSpan = fst (viewIntersectingB timeline factSpan)

viewIntersectingB :: TimelineB a -> FactSpan -> ([FactB a], TimelineB a)
viewIntersectingB = _

lookupIntersectingBVal :: TimelineBVal a -> FactSpan -> [FactBVal a]
lookupIntersectingBVal timeline factSpan = fst (viewIntersectingBVal timeline factSpan)

viewIntersectingBVal :: TimelineBVal a -> FactSpan -> ([FactBVal a], TimelineBVal a)
viewIntersectingBVal = _

lookupIntersectingBOf :: (item -> FactSpan) -> TimelineBOf init item -> FactSpan -> [item]
lookupIntersectingBOf itemToSpan timeline factSpan = fst (viewIntersectingBOf itemToSpan timeline factSpan)

viewIntersectingBOf :: (item -> FactSpan) -> TimelineBOf init item -> FactSpan -> ([item], TimelineBOf init item)
viewIntersectingBOf = _

class LookupIntersectingE span where
    lookupIntersectingE :: TimelineE a -> span -> [FactE a]
    lookupIntersectingE timeline factSpan = fst (viewIntersectingE timeline factSpan)
    viewIntersectingE :: TimelineE a -> span -> ([FactE a], TimelineE a)
instance LookupIntersectingE FactSpan where
    lookupIntersectingE = _
instance LookupIntersectingE FactSpanE where
    lookupIntersectingE = _