{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wincomplete-uni-patterns #-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module GateRep where
    -- ( Behavior
    -- , listToB
    -- , listToBI

    -- , Event
    -- , Occ (..)
    -- , listToE
    -- , updatesToEvent
    -- , updatesToEvent'
    -- , eventToList
    -- , never
    -- , once

    -- -- * Querying
    -- , lookupB

    -- -- * Combinators
    -- , step
    -- , stepI
    -- , leftmost

    -- -- * Partial Behviors/Events
    -- , MaybeKnown (..)
    -- , BehaviorPart
    -- , EventPart
    -- , listToEPart

    -- -- * Time Spans (TODO move to Time module)
    -- , Span
    -- , spanIncExc
    -- , endsOn

    -- -- ** Convenient Span construction.
    -- , allT
    -- , spanToExc             -- ^ Usually use this AND
    -- , spanFromInc           -- ^ Usually use this AND
    -- , spanFromIncToExc      -- ^ Usually use this

    -- , spanToInc
    -- , spanFromExc
    -- , spanFromExcToInc

    -- , spanFromIncToInc
    -- , spanFromExcToExc

    -- -- * Span operations
    -- , Intersect (..)
    -- , Difference (..)

    -- -- * Interfacing with the real world
    -- , sourceEvent
    -- , watchB
    -- , watchLatestB
    -- , watchLatestBIORef

    -- -- Internal (Exposed for testing)
    -- , LeftSpace
    -- , RightSpace
    -- , AllOr (..)

    -- -- * Quick Check
    -- , OrderedFullUpdates (..)
    -- ) where

import Control.Applicative
import Control.Concurrent
import Control.Concurrent.STM
import qualified Control.Concurrent.Chan as C
import Control.Monad (forever, forM, forM_)
import Data.Either (partitionEithers)
import Data.IORef
import Data.List (find, foldl', group, nub, partition, sort)
import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust, isNothing, mapMaybe)
import qualified Data.Map as M
import qualified Data.Set as S
import Test.QuickCheck hiding (once)

import Time
import TimeSpan


-- REFACTOR The problem is that you can represent things just after a ajust
-- after
--
--   Split (Value "a") (X_JustAfter 2) (Split (Value "b") (X_Exactly 2) (Value
--   "c"))
--
-- You can't represent the range of time that pplies to "b"! (X_JustAfter 2) is
-- NOT the correct start time if considered inclusive. It is the *exclusive*
-- start time of "c", but that what is the value at (X_JustAfter 2)? It is it
-- "a" or is it "b"? Both in a way!
--
-- The solution
--
-- In Split, use TimeD only, and make it the *inclusive* start time of right
-- and the *exclusive* start time of left. Still Use TimeX to track the
-- inclusive-inclusive min-max range of a value.

-- | Represents values at all times from -Inf to Inf
-- A tree structure, but semanticaly is a list of `Time`s with possible changes happening at and just after that time.
-- Note on lazyness: the depth corresponds to order of knowlage, so parent nodes can always be evaluated before the child nodes.
data Behavior a = Behavior a (Changes a) -- ^ initial value and value changes
    deriving (Functor, Show)
data Changes a
    = NoChanges
    | Changes
        (Changes a)     -- ^ Values strictly before t.
        Time             -- ^ Some t
        (Maybe a)        -- ^ Possible change of value at (inluding) t.
        (Maybe a)        -- ^ Possible change of value just after t.
        (Changes a)     -- ^ Value changes strictly after t.
    deriving (Functor, Show)

instance Eq a => Eq (Behavior a) where
    a == b = alwaysB (==True) ((==) <$> a <*> b)

-- | Requires full evaluation
alwaysB :: (a -> Bool) -> Behavior a -> Bool
alwaysB f b = all f allVals
    where
    (aInit, tas) = bToList b
    allVals = aInit : (snd <$> tas)

bToList :: Behavior a -> (a, [(TimeD, a)])
bToList (Behavior a cs) = (a, go cs)
    where
    go NoChanges = []
    go (Changes left t at atx right) = go left ++ catMaybes [(D_Exactly t,) <$> at, (D_JustAfter t,) <$> atx] ++ go right

-- -- | Basically a step function where you control the TimeX (inclusive) that value start.
-- listToBX :: a -> [(TimeD, a)] -> Behavior a
-- listToBX initA0 [] = (Value initA0)
-- listToBX initA0 ((initET, initEA):events) = Split (Value a) initET (listToBX initEA events)

changesFinalValue :: Changes a -> Maybe a
changesFinalValue NoChanges = Nothing
changesFinalValue (Changes l _ a b r) = changesFinalValue r <|> b <|> a <|> changesFinalValue l

instance Applicative Behavior where
    pure a = Behavior a NoChanges
    (<*>) ::forall a b . Behavior (a -> b) -> Behavior a -> Behavior b
    (Behavior fInitTop ftop) <*> (Behavior aInitTop atop)
        = let (bInit, bcs, _, _, _) = go allT fInitTop ftop aInitTop atop
           in Behavior bInit bcs
        where
        go :: SpanExc               -- ^ Span of f
           -> (a -> b)              -- ^ `f` at the start of this span
           -> Changes (a -> b)      -- ^ `f` changes within the span of f.
        --    -> SpanExc               -- ^ Span of the `a` changes. Contains the span of f
           -> a                     -- ^ `a` at the start of the `a` span
           -> Changes a             -- ^ `a` changes within the span of a.
           -> (b, Changes b, (a->b), a, b)
                                    -- ^ ( `b` at the start of this span
                                    --   , all b changes exactly in this span.
                                    --   , `f`,`x`,`b` at the end of this span )
        go _ f NoChanges x NoChanges = let fx = f x in (fx, NoChanges, f, x, fx)
        go _ f fcs x NoChanges = let
            fx = f x
            bcs = ($x) <$> fcs
            in (fx, bcs, fromMaybe f (changesFinalValue fcs), x, fromMaybe fx (changesFinalValue bcs))
        go fspan f NoChanges x xcs = let
            (xcs', xEnd) = crop fspan x xcs
            fx = f x
            bcs = f <$> xcs'
            in (fx, bcs, f, xEnd, fromMaybe fx (changesFinalValue bcs))
        -- TODO reduce xcs if possible here (i.e. if fspan is entirely to the left or right of the xcs split, then traverse xcs)
        go fspan
            f     (Changes fl fSplitTime ft ftx fr)
            x xcs@(Changes xl xSplitTime xt xtx xr)
            | fSplitTime == xSplitTime = let
                -- bt = fromMaybe (flEnd xlEnd) (($xlEnd) <$> ftx)
                -- btx = ($x) <$> ftx
                bt = (ft <*> xt) <|> (($x) <$> ft) <|> (f <$> xt)
                btx = (ftx <*> xtx) <|> (($(fromMaybe x xt)) <$> ftx) <|> ((fromMaybe f ft) <$> xtx)
                (b, bl, flEnd, xlEnd, _) = go lspan f fl x xl
                ftxx = fromMaybe flEnd $ ftx <|> ft
                xtxx = fromMaybe xlEnd $ xtx <|> xt
                (_, br, fEnd, xEnd, bEnd) = go rspan ftxx fr xtxx xr
                in (b, Changes bl fSplitTime bt btx br, fEnd, xEnd, bEnd)
            | otherwise = let
                bt  = ($xlEnd) <$> ft
                btx = ($xlEnd) <$> ftx
                (b, bl, flEnd, xlEnd, _) = go lspan f fl x xcs
                ftxx = fromMaybe flEnd $ ftx <|> ft
                (_, br, fEnd, xEnd, bEnd) = go rspan ftxx fr x xcs
                in (b, Changes bl fSplitTime bt btx br, fEnd, xEnd, bEnd)
            where
                (lspan, rspan) = splitSpanExcAtErr fspan fSplitTime

        crop :: SpanExc     -- ^ span to crop to
             -> d           -- ^ start value of this span
             -> Changes d   -- ^ changes spanning the span and possibly more.
             -> (Changes d, d)
                            -- ^ ( all d changes exactly in this span.
                            --   , `d` at the end of this span )
        crop _ bInit NoChanges = (NoChanges, bInit)
        crop tspan bInit (Changes l t bt btx r) = case splitSpanExcAt tspan t of
            FullyLeftOfT  tspan' -> crop tspan' bInit l
            FullyRightOfT tspan' -> crop tspan' (fromMaybe bInit $ btx <|> bt <|> changesFinalValue l) r
            SplitByT lspan rspan -> let
                (l', bMid) = crop lspan bInit l
                (r', bEnd) = crop rspan (fromMaybe bMid $ btx <|> bt) r
                in (Changes l' t bt btx r', bEnd)

-- -- | Basically a (immediate) step function but more convenient fr creating behaviors.
-- listToBI :: a -> [(Time, a)] -> Behavior a
-- listToBI initA events = stepI initA (listToE events)

-- -- | Basically a (delayed) step function but more convenient fr creating behaviors.
-- listToB :: a -> [(Time, a)] -> Behavior a
-- listToB initA events = step initA (listToE events)

instance Delayable (Behavior a) where
    delay (Behavior a cs) = Behavior a (delay cs)
instance Delayable (Changes a) where
    delay NoChanges = NoChanges
    delay (Changes l t at atx r) = Changes (delay l) t Nothing (atx <|> at) (delay r)

{-

-- | Crop values, leaving the value at the edges of the Span to expand to infinity.
cropOpen :: Span -> Behavior a -> Behavior a
cropOpen _ v@(Value _) = v
cropOpen tspan (Split left t right) = case splitSpanAt tspan t of
    (Nothing, Nothing) -> error "Impossible!"
    (Just lspan, Nothing) -> cropOpen lspan left
    (Nothing, Just rspan) -> cropOpen rspan right
    (Just lspan, Just rspan) -> Split (cropOpen lspan left) t (cropOpen rspan right)

-}
-- | No Maybe! because in this system, it will just block if the value is unknown.
lookupB :: TimeX -> Behavior a -> a
lookupB t (Behavior aInitTop cs) = go aInitTop cs
    where
    go aInit NoChanges = aInit
    go aInit (Changes left t' atM atxM right)
        | t < toTime t'         = go aInit left
        | toTime      t' == t   = at
        | X_JustAfter t' == t   = atx
        | otherwise             = go aInit right
        where
        aL = go aInit left
        at = fromMaybe aL atM
        atx = fromMaybe at atxM

-- | Event occurence
data Occ a = NoOcc | Occ a
    deriving (Eq, Show, Functor)

newtype Event a = Event { unEvent :: Changes (Occ a) }
    deriving (Show, Functor)

-- instance Show a => Show (Event a) where
--     show e = "Event " ++ show (eventToList e)

never :: Event a
never = Event NoChanges

once :: Time -> a -> Event a
once t a = listToE [(t, a)]

listToE :: [(Time, a)] -> Event a
listToE cs = Event (go cs)
    where
    go [] = NoChanges
    go ((t, a):tas) = Changes NoChanges t (Just (Occ a)) (Just NoOcc) (go tas)

eventToList :: Event a -> [(Time, a)]
eventToList (Event cs) = go cs
    where
    go :: Changes (Occ a) -> [(Time, a)]
    go NoChanges = []
    go (Changes l t at atx r) = case (at, atx) of
        (_, Just (Occ _)) -> error "eventToList: Found delayed event occurence"
        (Just _, Nothing) -> error "eventToList: unexpected (Changes _ _ (Just _) NoOcc _). We should always know the just after value for events."
        (Nothing, Nothing)    -> go l ++ go r
        (Nothing, Just NoOcc) -> go l ++ go r
        (Just occMay, Just NoOcc) -> go l ++ [(t,a) | Occ a <- [occMay]] ++ go r

-- Delayed step.
step :: a -> Event a -> Behavior a
step aInit (Event cs) = Behavior aInit (go cs)
    where
    go NoChanges = NoChanges
    go (Changes l t at atx r) = let nullRes = Changes (go l) t Nothing Nothing (go r)
        in case (at, atx) of
            (_, Just (Occ _)) -> error "eventToList: Found delayed event occurence"
            (Just _, Nothing) -> error "eventToList: unexpected (Changes _ _ (Just _) NoOcc _). We should always know the just after value for events."
            (Nothing, Nothing) -> nullRes
            (Nothing, Just NoOcc) -> nullRes
            (Just (Occ a), Just NoOcc) -> Changes (go l) t Nothing (Just a) (go r)
            (Just NoOcc  , Just NoOcc) -> Changes (go l) t Nothing Nothing (go r)

-- Immediate variant of step.
stepI :: forall a . a -> Event a -> Behavior a
stepI aInit (Event cs) = Behavior aInit (go cs)
    where
    go NoChanges = NoChanges
    go (Changes l t at atx r) = let nullRes = Changes (go l) t Nothing Nothing (go r)
        in case (at, atx) of
            (_, Just (Occ _)) -> error "eventToList: Found delayed event occurence"
            (Just _, Nothing) -> error "eventToList: unexpected (Changes _ _ (Just _) NoOcc _). We should always know the just after value for events."
            (Nothing, Nothing) -> nullRes
            (Nothing, Just NoOcc) -> nullRes
            (Just (Occ a), Just NoOcc) -> Changes (go l) t (Just a) Nothing (go r)
            (Just NoOcc  , Just NoOcc) -> Changes (go l) t Nothing Nothing (go r)

{-
-- | take the left most of simultaneous events
leftmost :: [Event a] -> Event a
leftmost es = foldl' const never es

--
-- Explicitly partial versions of Behavior/Event
--

data MaybeKnown a = Unknown | Known a
    deriving (Show)
type BehaviorPart a = Behavior (MaybeKnown a)
newtype EventPart a = EventPart { unEventPart :: BehaviorPart (Occ a) }
    deriving (Show)

behaviorPart :: Span -> a -> BehaviorPart a
behaviorPart (Span All All) a = Value (Known a)
behaviorPart (Span (Or (RightSpace lo)) (Or (LeftSpace hi))) a = Split (Value Unknown) lo (Split (Value $ Known a) hi (Value Unknown))
behaviorPart (Span All (Or (LeftSpace hi))) a = Split (Value $ Known a) hi (Value Unknown)
behaviorPart (Span (Or (RightSpace lo)) All) a = Split (Value Unknown) lo (Value $ Known a)
-}
-- | Assumes a finite input list.
-- Errors if there are overlapping time spans, or any event occurences appear outside of the span.
listToEPartsExcInc :: forall a . Time -> Time -> [(Time, a)] -> [EventPart a]
listToEPartsExcInc lo hi xs
    | let ts = lo : ((fst <$> xs) ++ [hi])
    , all (uncurry (<)) (zip ts (tail ts))
        =  error $ "listToEPartsExcInc: time not strictly increasing: " ++ show ts
    | otherwise = go lo xs
    where
    go t []
        | t == hi   = []
        | otherwise = [ChangesPart_NoChange (spanExc (Just t) (Just hi))]
    go t ((t', a):xs')
        = ChangesPart_NoChange (spanExc (Just t) (Just t'))
        -- ^^^ note it's safe to use spanExc because we checked tha t is strictly increasing.
        : ChangesPart_Change t' (Just (Occ a)) (Just NoOcc)
        : go t' xs'

-- | Assumes a finite input list.
-- Errors if there are overlapping time spans, or any event occurences appear outside of the span.
listToEPartsNegInfToInc :: forall a . Time -> [(Time, a)] -> [EventPart a]
listToEPartsNegInfToInc hi [] = [ ChangesPart_NoChange (spanExc Nothing (Just hi))
                                , ChangesPart_Change hi Nothing Nothing
                                ]
listToEPartsNegInfToInc hi ((lo, a):xs)
    = ChangesPart_NoChange (spanExc Nothing (Just lo))
    : ChangesPart_Change lo (Just (Occ a)) (Just NoOcc)
    : listToEPartsExcInc lo hi xs

{-
lookupMaxBPart :: forall a . BehaviorPart a -> Maybe (TimeX, a)
lookupMaxBPart btop = go allT btop
    where
    go :: Span -> BehaviorPart a -> Maybe (TimeX, a)
    go tspan (Value (Known a)) = Just (snd (spanToIncInc tspan), a)
    go _     (Value Unknown  ) = Nothing
    go tspan (Split l t r) = let (lspan, rspan) = splitSpanAtErr tspan t "lookupMaxBPart"
                              in go rspan r <|> go lspan l

unionBP :: BehaviorPart a -> BehaviorPart a -> BehaviorPart a
unionBP aB bB =
    ( \ a b -> case (a, b) of
        (Unknown, _) -> b
        (_, Unknown) -> a
        (Known _, Known _) -> error "unionBP: Knowlage overlap"
    ) <$> aB <*> bB

knownSpansE :: EventPart a -> [(Span, Event a)]
knownSpansE (EventPart b) = fmap Event <$> knownSpansB b

knownSpansB :: BehaviorPart a -> [(Span, Behavior a)]
knownSpansB btop = go allT btop
    where
    -- This is very similar to eventToList
    go :: Span -> Behavior (MaybeKnown a) -> [(Span, Behavior a)]
    go _     (Value Unknown) = []
    go tspan (Value (Known a)) = [(tspan, Value a)]
    go tspan (Split l t r) = let
        (lspan, rspan) = splitSpanAtErr tspan t "knownSpansB"
        spansL = go lspan l
        spansR = go rspan r
        in if null spansL
            then spansR
            else if null spansR
                then spansL
                else let
                    (lastLSpan,lastLB) = last spansL
                    (headRSpan,headRB) = head spansR
                    in case lastLSpan `endsOn` headRSpan of
                        Just (midSpan, midT) ->  init spansL ++ [(midSpan, Split lastLB midT headRB)] ++ tail spansR
                        Nothing -> spansL ++ spansR


--
-- IO stuff
--

chanToEvent :: Chan (EventPart a) -> IO (Event a)
chanToEvent inputChan = do
    updates <- C.getChanContents inputChan
    return (updatesToEvent updates)

-- eventToChan :: Event a -> IO (Chan (EventPart a))
-- eventToChan e = do
--     let b = unEvent e
--     watchB b

-}
sourceEvent
    :: forall a
    .  IO ([EventPart a] -> IO ()
          -- ^ Update the event
          , Event a
          )
sourceEvent = do
    -- TODO make this more efficient! We probably need to optimize for appending to the end of the known time.
    updatesChan <- C.newChan
    knowlageCoverTVar <- newTVarIO ( M.empty  -- Map from known time tspan low (exclusive) to TimeSpanExc
                                   , S.empty  -- Set of know instants
                                   )
    let updater :: [EventPart a] -> IO ()
        updater parts = do
            -- TODO can we use updatesToEvent' and observe the returned overlapping values instead of tracking them here?
            -- Check for overlap with knowlage
            hasOverlapMay <- atomically $ do
                (knownSpans, knownTimes) <- readTVar knowlageCoverTVar
                let findOverlap (ChangesPart_NoChange tspan) =
                        let lo = fst (spanExcBoundaries tspan)
                            prevSpanMay = snd <$> M.lookupLE lo knownSpans
                            nextSpanMay = snd <$> M.lookupGE lo knownSpans
                            overlapStr s = "(existing, new) = " ++ show s
                        in if maybe False (`intersects` tspan) prevSpanMay
                            then Just (overlapStr (fromJust prevSpanMay))
                            else if maybe False (`intersects` tspan) nextSpanMay
                                then Just (overlapStr (fromJust nextSpanMay))
                                else Nothing
                    findOverlap (ChangesPart_Change t _ _) = if S.member t knownTimes
                            then Just (show $ "existing = new = " ++ show t) else Nothing
                case mapMaybe findOverlap parts of
                    [] -> do
                        forM_ parts $ \ part -> case part of
                            -- insert new entries
                            ChangesPart_NoChange tspan -> do
                                let (t,_) = spanExcBoundaries tspan
                                modifyTVar knowlageCoverTVar (\(m, s) -> (M.insert t tspan m, s))
                            ChangesPart_Change t _ _ ->
                                modifyTVar knowlageCoverTVar (\(m, s) -> (m, S.insert t s))
                        return Nothing
                    xs -> return . Just $ "Source Event: update overlaps existing knowlage: " ++ unwords xs

            case hasOverlapMay of
                Just err -> fail err
                Nothing -> return ()
            mapM_ (C.writeChan updatesChan) parts
    updates <- C.getChanContents updatesChan
    let event = updatesToEvent updates
    return ( updater
           , event
           )

updatesToEvent :: [EventPart a] -> Event a
updatesToEvent = fst . updatesToEvent'

updatesToEvent'
    :: forall a
    .  [EventPart a]
    -> ( Event a            -- ^ The event.
       , [(SpanExc, EventPart a)]  -- ^ Event Parts that overlapped with previous event parts.
       )
updatesToEvent' updates = (Event occs, errCases)
    where
    (occs, _, errCases) = go allT (updates)

    go :: SpanExc
       -- ^ span of the resulting changes.
       -> [EventPart a]
       -- ^ Must all be in the span
       -> (Changes (Occ a), [EventPart a], [(SpanExc, EventPart a)])
       -- ^ Final Changes for the span, unused (non-overlapping) parts, unused overlapping parts
       -- TODO Use diff lists
    go tspan allPs = case allPs of
        [] -> (NoChanges, [], [])
        (p:ps) -> if not (isInSpan tspan p)
            then let (cs, others, overlapping) = go tspan ps
                  in (cs, p:others, overlapping)
            else case p of
                ChangesPart_Change t at atx -> let
                    (lspan, rspan) = splitSpanExcAtErr tspan t
                    (r, ps' , overlaps) = go rspan ps
                    (l, ps'', overlaps') = go lspan (ps')
                    in (Changes l t at atx r, ps'', overlaps ++ overlaps')
                ChangesPart_NoChange noChangeSpan -> case tspan `difference` noChangeSpan of
                    -- (Maybe (SpanExc, Time), Maybe (Time, SpanExc))
                    (Nothing, Nothing) -> let
                        (ps', overlap) = partition (not . isInSpan noChangeSpan) ps
                        in (NoChanges, ps', (tspan,) <$> overlap)
                    (Just (lspan, tl), Nothing) -> let
                        (ps', overlapsR) = partition (not . isInSpan noChangeSpan) ps
                        (atl, atlx, ps'', overlapsTL) = siphonChange tl ps'
                        (l, ps'2, overlapsL) = go lspan ps''
                        in ( Changes l tl atl atlx NoChanges
                           , ps'2
                           , ((noChangeSpan,) <$> overlapsR)
                                   ++ overlapsTL
                                   ++ overlapsL
                           )
                    (Nothing, Just (tr, rspan)) -> let
                        (r, ps', overlapsR) = go rspan ps
                        (atr, atrx, ps'', overlapsTR) = siphonChange tr ps'
                        (ps'2, overlapsL) = partition (not . isInSpan noChangeSpan) ps''
                        in ( Changes NoChanges tr atr atrx r
                           , ps'2
                           , overlapsR
                                   ++ overlapsTR
                                   ++ ((noChangeSpan,) <$> overlapsL)
                           )
                    (Just (lspan, tl), Just (tr, rspan)) -> let
                        -- Right
                        (r, ps'1, overlapsR) = go rspan ps
                        (atr, atrx, ps'2, overlapsTR) = siphonChange tr ps'1
                        (ps'3, overlapsMid) = partition (not . isInSpan noChangeSpan) ps'2
                        -- Left
                        (atl, atlx, ps'4, overlapsTL) = siphonChange tl ps'3
                        (l, ps'5, overlapsL) = go lspan ps'4
                        in ( Changes (Changes l tl atl atlx NoChanges) tr atr atrx r
                        , ps'5
                        , overlapsR
                                ++ overlapsTR
                                ++ ((noChangeSpan,) <$> overlapsMid)
                                ++ overlapsTL
                                ++ overlapsL
                        )
      where

      isInSpan :: SpanExc -> EventPart a -> Bool
      isInSpan s (ChangesPart_Change t _ _) = s `contains` t
      isInSpan s (ChangesPart_NoChange s')   = s `contains` s'

      siphonChange :: Time -> [EventPart a] -> (Maybe (Occ a), Maybe (Occ a), [EventPart a], [(SpanExc, EventPart a)])
      siphonChange t ps' = (at, atx, ps'', (\(p',_,_) -> (tspan, p')) <$> overlaps)
            where
            (at, atx, overlaps) = case siphoned of
                                    [] -> let err = error $ "updatesToEvent: Missing change value at time " ++ show t
                                          in (err, err, [])
                                    (_, at', atx'):overlaps'  -> (at', atx', overlaps')
            (siphoned, ps'') = partitionEithers
                            [case nextP of
                                ChangesPart_Change t' at' atx' | t' == t -> Left (nextP, at', atx')
                                _ -> Right nextP
                            | nextP <- ps' ]



    -- updates' = [ ks
    --             | update <- updates
    --             , ks <- knownSpansE update
    --             ]

    -- -- returns beh and remaining events to process
    -- go :: Span -> [(Span, Event a)] -> (Behavior (Occ a), [(Span, Event a)])
    -- go tspan [] = error $ "updatesToEvent: missing data for time span: " ++ show tspan
    -- go spanOut (x@(spanIn, (Event b)):xs)
    --     | not (spanOut `contains` spanIn)
    --         = let (b', xs') = go spanOut xs in (b', x:xs')
    --     | otherwise = case (spanOut `difference` spanIn) of
    --         (Nothing, Nothing) -> (b, xs)
    --         (Nothing, Just rspan) -> case rspan of
    --             Span (Or (RightSpace t)) _ -> let
    --                 (rightB, xs') = go rspan xs
    --                 in (Split b t rightB, xs')
    --             _ -> diffErr
    --         (Just lspan, Nothing) -> case lspan of
    --             Span _ (Or (LeftSpace t)) -> let
    --                 (leftB, xs') = go lspan xs
    --                 in (Split leftB t b, xs')
    --             _ -> diffErr
    --         (Just lspan, Just rspan) -> case (lspan, rspan) of
    --             (Span _ (Or (LeftSpace tlo)), Span (Or (RightSpace thi)) _)
    --                 -> let
    --                 -- Let the right branch process xs first (optimize for appending to the right).
    --                 (rightB, xs') = go rspan xs
    --                 (leftB, xs'') = go lspan xs'
    --                 in (Split leftB tlo (Split b thi rightB), xs'')
    --             (_,_) -> diffErr
    --     where
    --     diffErr = error $ "Impossibe! After a `difference` the left span must end on Or and the right"
    --                 ++ "span must start on an Or, but got: difference (" ++ show spanOut ++ ") ("
    --                 ++ show spanIn ++ ") == " ++ show (difference spanOut spanIn)

-- | Watch a Behavior, sening data to a callback as they are evaluated.
-- A dedicated thread is created that will run the callback.
watchB
    :: forall a
    .  Behavior a
    -> (BehaviorPart a -> IO ())
    -- ^ IO function to call with partial behavior value.
    -- Will always be called on it's own thread and possibly concurrently.
    -- Note the value is lazy but the times are strict
    -> IO ThreadId
watchB btop notifyPart = forkIO $ do
    (_, chan) <- behaviorToChan btop
    -- do forever
    forever $ notifyPart =<< readChan chan

-- | Calls the call back a with the latest (time wise) available value.
-- A dedicated thread is created that will run the callback.
-- TODO because we don't have a value attached to BehaviorPart_NoChange we can't
-- send updates for the same a but with a more up to date time. So you only get
-- latest *change* time at the moment.
watchLatestB :: Behavior a -> ((TimeX, a) -> IO ()) -> IO ThreadId
watchLatestB b callback = forkIO $ do
    (_, chan) <- behaviorToChan b
    -- do forever
    let loop :: TimeX -> IO ()
        loop t = do
            part <- readChan chan
            t' <- case part of
                BehaviorPart_Init a
                    | t == X_NegInf -> t <$ callback (X_NegInf, a)
                BehaviorPart_ChangesPart (ChangesPart_Change t' atMay atxMay) -> case (atMay, atxMay) of
                    (_, (Just atx))
                        | let t'' = X_JustAfter t'
                        , t'' > t -> t'' <$ callback (t'', atx)
                    ((Just at), _)
                        | let t'' = X_Exactly   t'
                        , t'' > t -> t'' <$ callback (t'', at)
                    _  -> pure t
                -- TODO
                -- BehaviorPart_NoChange s
                --     | let t' = spanExcMaxT s
                --     , t' > t -> callback (t', _a)
                _ -> return t
            loop t'
    loop X_NegInf

-- TODO move to NFRP higher level api (because we assume X_NegInf is full)
-- | Note the initial value is the value at X_NegInf. Ensure this exists!
watchLatestBIORef :: Behavior a -> IO (ThreadId, IORef (TimeX, a))
watchLatestBIORef b@(Behavior aInit _) = do
    ref <- newIORef (X_NegInf, aInit)
    tid <- watchLatestB b (writeIORef ref)
    return (tid, ref)

type EventPart a = ChangesPart (Occ a)

data ChangesPart a
    = ChangesPart_Change Time (Maybe a) (Maybe a)
    | ChangesPart_NoChange SpanExc
    deriving (Show)

data BehaviorPart a
    = BehaviorPart_Init a
    | BehaviorPart_ChangesPart (ChangesPart a)
    deriving (Show)

behaviorToChan
    :: forall a
    .  Behavior a
    -- ^ IO function to call with partial behavior value.
    -- Will always be called on it's own thread and possibly concurrently.
    -- Note the value is lazy but the times are strict
    -> IO (ThreadId, Chan (BehaviorPart a))
behaviorToChan btop = do
    updatesChan <- newChan
    tid <- forkIO $ do
        _ <- forkIO $ case btop of
                Behavior a _ -> writeChan updatesChan (BehaviorPart_Init a)
        _ <- forkIO $ do
            let go :: SpanExc -> Changes a -> IO ()
                go tspan NoChanges = writeChan updatesChan (BehaviorPart_ChangesPart (ChangesPart_NoChange tspan))
                go tspan (Changes left t at atx right) = do
                    writeChan updatesChan (BehaviorPart_ChangesPart (ChangesPart_Change t at atx))
                    let (lspan, rspan) = splitSpanExcAtErr tspan t
                    _ <- forkIO $ go lspan left
                    go rspan right
            let Behavior _ cs = btop
            go allT cs
        return ()
    return (tid, updatesChan)
--
-- QuickCheck Stuff
--

instance Arbitrary a => Arbitrary (Changes a) where
    arbitrary = do
        times <- orderedList
        go (head <$> group times)
        where
        go :: [Time] -> Gen (Changes a)
        go [] = return NoChanges
        go ts = do
            sizeL <- choose (0,length ts - 1)
            l <- go (take sizeL ts)
            let t = ts !! sizeL
            r <- go (drop (sizeL + 1) ts)
            at <- arbitrary
            atx <- arbitrary
            return (Changes l t at atx r)

instance Arbitrary a => Arbitrary (Behavior a) where
    arbitrary = Behavior <$> arbitrary <*> arbitrary

instance Arbitrary a => Arbitrary (Occ a) where
    arbitrary = oneof [Occ <$> arbitrary, pure NoOcc]

instance Arbitrary a => Arbitrary (Event a) where
    arbitrary = do
        times <- orderedList
        Event <$> go (head <$> group times)
        where
        go :: [Time] -> Gen (Changes (Occ a))
        go [] = return NoChanges
        go ts = do
            sizeL <- choose (0,length ts - 1)
            l <- go (take sizeL ts)
            let t = ts !! sizeL
            r <- go (drop (sizeL + 1) ts)
            at <- arbitrary
            return (Changes l t at (NoOcc <$ at) r)
