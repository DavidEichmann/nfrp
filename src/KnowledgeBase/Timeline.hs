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
    ( TimelineE (..)
    , TimelineB (..)
    , TimelineBVal (..)
    , MultiTimeline

    , FactSpan

    , Fact' (..)
    , FactB
    , FactBVal
    , FactE
    , IsChange (..)

    , toFactSpan
    -- , LookupIntersectingE (..)
    , leftNeighbors
    , rightNeighbors
    -- , lookupIntersecting
    -- , lookupIntersectingBVal
    -- , lookupIntersectingBOf
    , lookupIntersecting
    , mtLookupIntersecting
    , viewIntersecting
    , mtViewIntersecting
    -- , viewIntersectingBVal
    -- , viewIntersectingBOf
    , insertFact
    , setValueForallFactB
    ) where

import Control.Monad (guard)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (isJust)
import Data.Void

import Time
import TimeSpan


--
-- Fact Span
--

-- Spans of time that can cover a single fact
data FactSpan
    = FS_Init
    -- ^ Just (Behavior) initial value
    | FS_Point Time
    -- ^ single point in time
    | FS_Span SpanExc
    -- ^ Span of time. `allT` does NOT include the (Behavior) initial value.
    | FS_All
    -- ^ All time including the (Behavior) initial value.


--
-- Fact
--

data Fact' initT pointT spanT
    = Init initT
    | ChangePoint Time pointT
    | ChangeSpan SpanExc spanT

type FactB     a = Fact' a (MaybeChange a) NoChange
type FactBVal  a = Fact' a a (NoChangeVal a)
type FactE     a = Fact' Void (Maybe a) NoChange

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
instance (IsChange pd, IsChange sd) => IsChange (Fact' id pd sd) where
    isChange (Init _) = True
    isChange (ChangePoint _ f) = isChange f
    isChange (ChangeSpan _ f) = isChange f
instance IsChange (MaybeChange a) where
    isChange = isJust . unMaybeChange
instance IsChange (NoChangeVal a) where
    isChange _ = False
instance IsChange NoChange where
    isChange _ = False

toFactSpan :: Fact' a b c -> FactSpan
toFactSpan (Init _) = FS_Init
toFactSpan (ChangePoint t _) = FS_Point t
toFactSpan (ChangeSpan tspan _) = FS_Span tspan

-- Replace all facts with the given value.
setValueForallFactB :: a -> FactB a -> FactBVal a
setValueForallFactB a (Init _) = Init a
setValueForallFactB a (ChangePoint t _) = ChangePoint t a
setValueForallFactB a (ChangeSpan tspan _) = ChangeSpan tspan (NoChangeVal a)


--
-- Timeline
--

data Timeline initT pointT spanT = Timeline (Maybe initT) (Map TimeX (Fact' initT pointT spanT))
newtype TimelineB     a = TimelineB    { unTimelineB    :: Timeline a    (MaybeChange a) NoChange        }
newtype TimelineBVal  a = TimelineBVal { unTimelineBVal :: Timeline a    a               (NoChangeVal a) }
newtype TimelineE     a = TimelineE    { unTimelineE    :: Timeline Void (Maybe a)       NoChange        }

-- Timeline with overlapping FactSpans
data MultiTimeline a = MultiTimeline [a] (Map TimeX [a])

insertFact :: Fact' id pd sd -> Timeline id pd sd -> Timeline id pd sd
insertFact f timelineB@(Timeline initAMay factMap)
    | not $ null $ lookupIntersecting timelineB $ toFactSpan f
        = error "insertFactB: overlapping fact."
    | otherwise = case f of
        Init a -> Timeline (Just a) factMap
        ChangePoint t _ -> Timeline initAMay (Map.insert (toTime t) f factMap)
        ChangeSpan tspan _ -> Timeline initAMay (Map.insert (spanExcMinT tspan) f factMap)

lookupIntersecting :: Timeline id pd sd -> FactSpan -> [Fact' id pd sd]
lookupIntersecting timeline factSpan = fst (viewIntersecting timeline factSpan)

viewIntersecting :: Timeline id pd sd -> FactSpan -> ([Fact' id pd sd], Timeline id pd sd)
viewIntersecting timeline factSpan = _

mtLookupIntersecting :: (a -> FactSpan) -> MultiTimeline a -> FactSpan -> [a]
mtLookupIntersecting aToFactSpan multiTimeline factSpan = fst (mtViewIntersecting aToFactSpan multiTimeline factSpan)

mtViewIntersecting :: (a -> FactSpan) -> MultiTimeline a -> FactSpan -> ([a], MultiTimeline a)
mtViewIntersecting aToFactSpan (MultiTimeline inits m) fs = case fs of
    _ -> _

-- | Get all right neighbors starting just after the end of the given FactSpan.
rightNeighbors :: forall id pd sd
    .  Timeline id pd sd
    -> FactSpan
    -- ^ Current fact span. First neighbor start is just after the start of this fact span.
    -> [Fact' id pd sd]
rightNeighbors kBFactsB@(Timeline _ m) currFactSpan = case nextFactMay of
    Nothing -> []
    Just nextFact -> nextFact : rightNeighbors kBFactsB (toFactSpan nextFact)
    where
    nextFactMay :: Maybe (Fact' id pd sd)
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
        FS_All -> Nothing
leftNeighbors :: forall id pd sd
    .  Timeline id pd sd
    -> FactSpan
    -- ^ Current fact span. First neighbor end is just before the start of this fact span.
    -> [Fact' id pd sd]
leftNeighbors timeline@(Timeline initA m) currFactSpan = case prevCFactMay of
    Nothing -> []
    Just prevCFact -> prevCFact : leftNeighbors timeline (toFactSpan prevCFact)
    where
    prevCFactMay :: Maybe (Fact' id pd sd)
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
        FS_All -> Nothing

{-}
lookupBValJustBefore :: FactSpan -> TimelineBVal a -> Maybe a
lookupBValJustBefore = _ -- leftNeighbors
-}

isLeftNeighborOf :: FactSpan -> FactSpan -> Bool
isLeftNeighborOf left right = _