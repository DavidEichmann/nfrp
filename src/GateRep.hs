{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

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
import Control.Monad (forever, forM)
import Data.IORef
import Data.List (find, foldl', group, nub, sort)
import Data.Maybe (catMaybes, fromJust, fromMaybe, isJust)
import qualified Data.Map as M
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
        = let (bInit, bcs, _, _, _) = go allT allT fInitTop ftop allT aInitTop atop
           in Behavior bInit bcs
        where
        go :: SpanExc               -- ^ Span of the output we want to produce
           -> SpanExc               -- ^ Span of the `f` changes. Contains the output span.
           -> (a -> b)              -- ^ `f` at the start of this span
           -> Changes (a -> b)      -- ^ Superset of `f` changes within the span.
           -> SpanExc               -- ^ Span of the `a` changes. Contains the output span.
           -> a                     -- ^ `a` at the start of this span
           -> Changes a             -- ^ Superset of `a` changes within the span.
           -> (b, Changes b, (a->b), a, b)
                                    -- ^ ( `b` at the start of this span
                                    --   , all b changes exactly in this span.
                                    --   , `f`,`x`,`b` at the end of this span )
        go _ _ f NoChanges _ x NoChanges = let fx = f x in (fx, NoChanges, f, x, fx)
        go tspan _ f fcs _ x NoChanges = let
            fx = f x
            (_, cropf, fEnd) = crop tspan f fcs
            bcs = ($x) <$> cropf
            in (fx, bcs, fromMaybe f (changesFinalValue fcs), x, fromMaybe fx (changesFinalValue bcs))
        go tspan _ f NoChanges _ x xcs = _ -- crop tspan (f x) (f <$> xcs)
        go tspan
            fspan f fcs@(Changes fl fSplitTime ft ftx fr)
            xspan x xcs@(Changes xl xSplitTime xt xtx xr)
            = case (splitSpanExcAt tspan fSplitTime, splitSpanExcAt tspan xSplitTime) of
                -- Recurse untill fSplitTime and xSplitTime are within tspan.
                (FullyLeftOfT  _, _) -> go tspan _fspan' f fl _xspan x xcs
                (FullyRightOfT _, _) -> go tspan _fspan' fInitR fr _xspan x xcs
                (_, FullyLeftOfT  _) -> go tspan _fspan f fcs _xspan' x xl
                (_, FullyRightOfT _) -> go tspan _fspan f fcs _xspan' xInitR xr
                --fSplitTime and xSplitTime are within tspan.
                (SplitByT flspan frspan, SplitByT xlspan xrspan) -> if fSplitTime == xSplitTime
                    then let
                        bSplitTime = fSplitTime -- == xSplitTime
                        lspan = flspan -- == xlspan
                        rspan = frspan -- == xrspan
                        (_, bl, flEnd, xlEnd, blEnd) = go lspan _fspan'l f fl _xspan'l x xl
                        (bt, btx, _) = btBtx flEnd ft ftx xlEnd xt xtx
                        (ft, ftx, f) = btBtx flEnd ft ftx xlEnd xt xtx
                        (bt, btx, _) = btBtx flEnd ft ftx xlEnd xt xtx
                        (_, br, frEnd, xrEnd, brEnd) = go rspan _fspan'r fInitR fr _xspan'r xInitR xr
                        in (f x, Changes bl bSplitTime bt btx br, frEnd, xrEnd, brEnd)
                    else let
                        midSpan = if fSplitTime < xSplitTime
                                    then spanExc (Just fSplitTime) (Just xSplitTime)
                                    else spanExc (Just xSplitTime) (Just fSplitTime)
                        _ = go lspan _fspan' f fl _xspan' x xl
                        in case tspan `difference` midSpan of
                            (Nothing, Nothing) -> error $ "instance Applicative Behavior: Impossible! " ++ show tspan ++ " `difference` " ++ show midSpan ++ " == (Nothing, Nothing)"
                            -- Mid span is all the way to the right of tspan
                            (Just (lspan, midT), Nothing) -> let
                                midSplitTime = min fSplitTime xSplitTime
                                (bInit, bl, fMidInit, xMidInit, bMidInit) = go lspan _fspan' f fl _xspan' x xl
                                (bInitMid, br, fEnd, xEnd, bEnd) = go midSpan _fspan' f fl _xspan' x xl
                                (bMid, bMidx) = _
                                in (bInit, Changes bl midSplitTime bMid bMidx br, fEnd, xEnd, bEnd)
                            -- Mid span is all the way to the left of tspan
                            (Nothing, Just (midT, rspan)) -> _
                            -- There is space on both sides of mid span within tspan.
                            (Just (lspan, midTLo), Just (midTHi, rspan)) -> _

                where
                fInitR = fromMaybe f $ ftx <|> ft <|> changesFinalValue fl
                xInitR = fromMaybe x $ xtx <|> xt <|> changesFinalValue xl

        -- find the change and just after change (3rd and 4th arguments to Changes) and value after for b, f, and x
        -- value just before -> maybe change at t -> maybe change at just after t
        btBtx :: (a->b) -> Maybe (a->b) -> Maybe (a->b)
              -> a      -> Maybe a      -> Maybe a
              -> (Maybe b, Maybe b, b, (a->b), a)
        btBtx fInit ft ftx xInit xt xtx = (bt, btx, btxx)
            where
            bt = (ft <*> xt) <|> (($xInit) <$> ft) <|> (fInit <$> xt)
            btx = (ftx <*> xtx) <|> (($(fromMaybe xInit xt)) <$> ftx) <|> ((fromMaybe fInit ft) <$> xtx)
            btxx = fromMaybe fInit (btx <|> bt)
            ftxx = fromMaybe f $ ftx <|> ft <|> changesFinalValue fl
            xInitR = fromMaybe x $ xtx <|> xt <|> changesFinalValue xl

                -- if fSplitTime == xSplitTime
                -- then  let
                --         t = fSplitTime

                --         (_, l', bMid) = go tspan fspan fcs xspan x xcs
                --         (_, r', bEnd) = go rspan (fromMaybe bMid $ btx <|> bt) r
                --         in (bInit, Changes l' t bt btx r', bEnd)
                -- else _

                -- LT -> _
                -- EQ -> let
                --         t = fSplitTime
                --         lspan = Span
                --         (_, l', bMid) = go (tspan `intersect` LeftSpace t) bInit l
                --         (_, r', bEnd) = crop rspan (fromMaybe bMid $ btx <|> bt) r
                --         in (bInit, Changes l' t bt btx r', bEnd)
                -- GT -> _




        crop :: SpanExc     -- ^ span to crop to
             -> d           -- ^ start value of this span
             -> Changes d   -- ^ changes spanning the span and possibly more.
             -> (d, Changes d, d)
                            -- ^ ( `d` at the start of this span (== second arg)
                            --   , all d changes exactly in this span.
                            --   , `d` at the end of this span )
        crop _ bInit NoChanges = (bInit, NoChanges, bInit)
        crop tspan bInit (Changes l t bt btx r) = case splitSpanExcAt tspan t of
            FullyLeftOfT  tspan' -> crop tspan' bInit l
            FullyRightOfT tspan' -> crop tspan' (fromMaybe bInit $ btx <|> bt <|> changesFinalValue l) r
            SplitByT lspan rspan -> let
                (_, l', bMid) = crop lspan bInit l
                (_, r', bEnd) = crop rspan (fromMaybe bMid $ btx <|> bt) r
                in (bInit, Changes l' t bt btx r', bEnd)

        -- go (Value f) (Value x) = Value (f x)
        -- go fs (Value x)
        --     = ($x) <$> fs
        -- go (Value f) xs
        --     = f <$> xs
        -- go (Split fL fT fR) (Split xL xT xR) = case compare fT xT of
        --     EQ -> Split (fL <*> xL) fT (fR <*> xR)
        --     LT -> Split (fL <*> takeLeft fT xL)
        --                 fT
        --                 (Split (takeLeft xT fR <*> takeRight xT xL)
        --                        xT
        --                        (takeRight xT fR <*> xR)
        --                 )
        --     GT -> Split (takeLeft fT fL <*> xL)
        --                 xT
        --                 (Split (takeRight xT fR <*> takeLeft xT xL)
        --                        fT
        --                        (fR <*> takeRight xT xR)
        --                 )

        -- -- Includes t
        -- takeLeft :: TimeD -> Behavior a -> Behavior a
        -- takeLeft t (Split l t' r) = case compare t t' of
        --     EQ -> l
        --     LT -> takeLeft t l
        --     GT -> takeLeft t r
        -- takeLeft _ v = v

        -- -- Excludes t
        -- takeRight :: TimeD -> Behavior a -> Behavior a
        -- takeRight t (Split l t' r) = case compare t t' of
        --     EQ -> r
        --     LT -> takeRight t l
        --     GT -> takeRight t r
        -- takeRight _ v = v

{-
-- | Basically a (immediate) step function but more convenient fr creating behaviors.
listToBI :: a -> [(Time, a)] -> Behavior a
listToBI initA events = stepI initA (listToE events)

-- | Basically a (delayed) step function but more convenient fr creating behaviors.
listToB :: a -> [(Time, a)] -> Behavior a
listToB initA events = step initA (listToE events)

instance Delayable (Behavior a) where
    delay top = go top All
        where
        go :: Behavior a -> AllOr LeftSpace -> Behavior a
        go (Split left t right) rightBoundScope =
            let
            t' = delay t
            leftScope = Or (LeftSpace t')
            -- If there is already a next value at the delayed time, then discard the right value.
            in if rightBoundScope `contains` t'
                then Split (go left leftScope) t' (go right rightBoundScope)
                else go left leftScope
        go v _ = v

-- | Crop values, leaving the value at the edges of the Span to expand to infinity.
cropOpen :: Span -> Behavior a -> Behavior a
cropOpen _ v@(Value _) = v
cropOpen tspan (Split left t right) = case splitSpanAt tspan t of
    (Nothing, Nothing) -> error "Impossible!"
    (Just lspan, Nothing) -> cropOpen lspan left
    (Nothing, Just rspan) -> cropOpen rspan right
    (Just lspan, Just rspan) -> Split (cropOpen lspan left) t (cropOpen rspan right)

-- | No Maybe! because in this system, it will just block if the value is unknown.
lookupB :: TimeX -> Behavior a -> a
lookupB t b = go b
    where
    go (Value a) = a
    go (Split left t' right)
        | t < toTime t'  = go left
        | otherwise      = go right

-- | Event occurence
data Occ a = NoOcc | Occ a
    deriving (Eq, Show, Functor)

newtype Event a = Event { unEvent :: Behavior (Occ a) }
    deriving (Show, Functor)

-- instance Show a => Show (Event a) where
--     show e = "Event " ++ show (eventToList e)

never :: Event a
never = Event (Value NoOcc)

once :: Time -> a -> Event a
once t a = listToE [(t, a)]

listToE :: [(Time, a)] -> Event a
listToE [] = Event (Value NoOcc)
listToE ((t,a):es)
    = Event $ Split (Value NoOcc) (D_Exactly t)
        (Split (Value (Occ a)) (D_JustAfter t) (unEvent (listToE es)))

eventToList :: Event a -> [(Time, a)]
eventToList (Event b) = go allT b
    where
    go :: Span -> Behavior (Occ a) -> [(Time, a)]
    go _ (Value NoOcc) = []
    go tspan (Value (Occ a)) = case instantaneous tspan of
        Just occT -> [(occT, a)]
        Nothing -> error $ "eventToList: Found non-instantaneous event spanning time: " ++ show tspan
    go tspan (Split l t r) = go lspan l ++ go rspan r
        where
        (lspan, rspan) = splitSpanAtErr tspan t
                            "eventToList: found a Split with out of bounds time"

-- Delayed step.
step :: a -> Event a -> Behavior a
step aInit = delay . stepI aInit

-- Immediate variant of step.
stepI :: forall a . a -> Event a -> Behavior a
stepI initA0 (Event btop) = fst (go initA0 btop)
    where
    -- Remove NoOcc. If NoOcc return Nothing
    -- also return the value at the end of the tspan (if one exists)
    go :: a -> Behavior (Occ a) -> (Behavior a, a)
    go initA (Value NoOcc)   = (Value initA, initA)
    go _     (Value (Occ a)) = (Value a, a)
    go initA (Split left t right) = let
        (left', initA') = go initA left
        (right', endVal) = go initA' right
        -- Even though we could simplify the structure, we keep it so that we
        -- can return values more lazily. We dont necessarily need to know the
        -- whole (leftMay', prevValMay') to evaluate most of the right
        in (Split left' t right', endVal)

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

-- | Assumes a finite input list.
-- Errors if there are overlapping time spans, or any event occurences appear outside of the span.
listToEPart :: forall a . [(Span, [(Time, a)])] -> EventPart a
listToEPart spans = let
    knownBs :: [BehaviorPart (Occ a)]
    knownBs = [ let Event occsB = listToE occs
                    knowlage = cropOpen tspan (Known <$> occsB) -- cropOpen is needed to get rid of a possible final NoOcc at the end of tspan
                    unknown = Value Unknown
                 in case find (not . (tspan `contains`)) (fst <$> occs) of
                        Just errT -> error $ "listToEPart: found event at time (" ++ show errT ++ ") not in span (" ++ show tspan ++ ")"
                        Nothing -> case tspan of
                            Span All All -> knowlage
                            Span All (Or (LeftSpace t)) -> Split knowlage t unknown
                            Span (Or (RightSpace t)) All -> Split unknown t knowlage
                            Span (Or (RightSpace tlo)) (Or (LeftSpace thi)) -> Split (Split unknown tlo knowlage) thi unknown
            | (tspan, occs) <- spans
            ]
    in EventPart (foldl' unionBP (pure Unknown) knownBs)

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

sourceEvent :: IO (EventPart a -> IO ()
                  -- ^ Update the event
                  --      ( knowlage start Exclusive!
                  --      , event time
                  --      , event value
                  --      , knowlage stop Inclusive!
                  --      )
                  , Event a
                  )
sourceEvent = do
    -- TODO make this more efficient! We probably need to optimize for appending to the end of the known time.
    updatesChan <- C.newChan
    knowlageCoverTVar <- newTVarIO M.empty  -- Map from known time tspan low (exclusive) to that times tspan's hi (inclusive)
    let updater part = do
            -- TODO can we use updatesToEvent' and observe the returned overlapping values instead of tracking them here?
            -- Check for overlap with knowlage
            let partSpans :: [Span]
                partSpans = fst <$> knownSpansE part
            hasOverlapMay <- atomically $ do
                let loop [] = do
                            -- insert new entries
                            let partSpansMap = M.fromList [(fst (spanToIncInc s), s) | s <- partSpans]
                            modifyTVar knowlageCoverTVar (M.union partSpansMap)
                            return Nothing
                    loop (tspan:xs) = do
                        knowlageCover <- readTVar knowlageCoverTVar
                        let lo = fst (spanToIncInc tspan)
                            prevSpanMay = snd <$> M.lookupLE lo knowlageCover
                            nextSpanMay = snd <$> M.lookupGE lo knowlageCover
                        if maybe False (`intersects` tspan) prevSpanMay
                            then return (Just (tspan, fromJust prevSpanMay))
                            else if maybe False (`intersects` tspan) nextSpanMay
                                then return (Just (tspan, fromJust nextSpanMay))
                                else loop xs
                loop partSpans
            case hasOverlapMay of
                Just (existing, new)
                    -> fail $ "Source Event: updated overlaps existing knowlage. existing = "
                            ++ show existing
                            ++ ", new = "
                            ++ show new
                Nothing -> return ()
            C.writeChan updatesChan part
    updates <- C.getChanContents updatesChan
    let event = updatesToEvent updates
    return ( updater
           , event
           )


updatesToEvent :: [EventPart a] -> Event a
updatesToEvent = fst . updatesToEvent'

updatesToEvent'
    :: [EventPart a]
    -> ( Event a            -- ^ The event.
       , [(Span, Event a)]  -- ^ Event Parts that overlapped with previous event prts
       )
updatesToEvent' updates = (Event occsB, errCases)
    where
    (occsB, errCases) = go allT updates'
    updates' = [ ks
                | update <- updates
                , ks <- knownSpansE update
                ]

    -- returns beh and remaining events to process
    go :: Span -> [(Span, Event a)] -> (Behavior (Occ a), [(Span, Event a)])
    go tspan [] = error $ "updatesToEvent: missing data for time span: " ++ show tspan
    go spanOut (x@(spanIn, (Event b)):xs)
        | not (spanOut `contains` spanIn)
            = let (b', xs') = go spanOut xs in (b', x:xs')
        | otherwise = case (spanOut `difference` spanIn) of
            (Nothing, Nothing) -> (b, xs)
            (Nothing, Just rspan) -> case rspan of
                Span (Or (RightSpace t)) _ -> let
                    (rightB, xs') = go rspan xs
                    in (Split b t rightB, xs')
                _ -> diffErr
            (Just lspan, Nothing) -> case lspan of
                Span _ (Or (LeftSpace t)) -> let
                    (leftB, xs') = go lspan xs
                    in (Split leftB t b, xs')
                _ -> diffErr
            (Just lspan, Just rspan) -> case (lspan, rspan) of
                (Span _ (Or (LeftSpace tlo)), Span (Or (RightSpace thi)) _)
                    -> let
                    -- Let the right branch process xs first (optimize for appending to the right).
                    (rightB, xs') = go rspan xs
                    (leftB, xs'') = go lspan xs'
                    in (Split leftB tlo (Split b thi rightB), xs'')
                (_,_) -> diffErr
        where
        diffErr = error $ "Impossibe! After a `difference` the left span must end on Or and the right"
                    ++ "span must start on an Or, but got: difference (" ++ show spanOut ++ ") ("
                    ++ show spanIn ++ ") == " ++ show (difference spanOut spanIn)

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
watchLatestB :: Behavior a -> ((TimeX, a) -> IO ()) -> IO ThreadId
watchLatestB b callback = forkIO $ do
    (_, chan) <- behaviorToChan b
    -- do forever
    let loop t = do
            maxMay <- lookupMaxBPart <$> readChan chan
            case maxMay of
                Just (t', a) | t' > t -> do
                                    callback (t', a)
                                    loop t'
                _ -> loop t
    loop X_NegInf

-- TODO move to NFRP higher level api (because we assume X_NegInf is full)
-- | Note the initial value is the value at X_NegInf. Ensure this exists!
watchLatestBIORef :: Behavior a -> IO (ThreadId, IORef (TimeX, a))
watchLatestBIORef b = do
    ref <- newIORef (X_NegInf, lookupB X_NegInf b)
    tid <- watchLatestB b (writeIORef ref)
    return (tid, ref)


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
        let go :: Span -> Behavior a -> IO ()
            go tspan (Value a) = writeChan updatesChan (behaviorPart tspan a)
            go tspan (Split left t right) = case splitSpanAt tspan t of
                (Nothing, Nothing) -> error $ "Impossible! splitSpanAt " ++ show tspan ++ " = (Nothing, Nothing)"
                (Just lspan, Nothing) -> go lspan left
                (Nothing, Just rspan) -> go rspan right
                (Just lspan, Just rspan) -> do
                    _ <- forkIO $ go lspan left
                    go rspan right
        go allT btop
    return (tid, updatesChan)
-}

{-
--
-- QuickCheck Stuff
--

instance Arbitrary a => Arbitrary (Behavior a) where
    arbitrary = do
        times <- orderedList
        go (head <$> group times)
        where
        go :: [TimeD] -> Gen (Behavior a)
        go [] = Value <$> arbitrary
        go ts = do
            sizeL <- choose (0,length ts - 1)
            l <- go (take sizeL ts)
            let t = ts !! sizeL
            r <- go (drop (sizeL + 1) ts)
            return (Split l t r)


instance Arbitrary a => Arbitrary (Event a) where
    arbitrary = do
        times <- orderedList
        Event <$> go (nub times)
        where
        go :: [Time] -> Gen (Behavior (Occ a))
        go [] = pure (Value NoOcc)
        go ts = do
            sizeL <- choose (0,length ts - 1)
            l <- go (take sizeL ts)
            r <- go (drop (sizeL + 1) ts)
            a <- arbitrary
            let t = ts !! sizeL
            return (Split l (D_Exactly t) (Split (Value (Occ a)) (D_JustAfter t) r))

        -}