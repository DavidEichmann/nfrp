{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wincomplete-uni-patterns #-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
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

module FRP (
    -- * Combinators
      Behavior
    , alwaysB

    , Event
    , never
    , once
    , step

    -- * Event Sources / Observing in IO
    , sourceEvent
    , listToPartialE
    , watchE
    , watchB
    , watchLatestB
    , watchLatestBIORef


    -- * Convert to and from list.
    , behaviourToList
    , listToB
    , eventToList
    , listToE

    -- * Iternal Stuff
    , EventPart (..)
    , BehaviorPart (..)
    , PartialEvent
    , Occ (..)
    , updatesToEvent
    , updatesToEvent'
    , lookupB
    , OrderedFullEventParts (..)
    ) where

import           Data.Binary (Binary)
import           Control.Applicative
import           Control.Concurrent
import           Control.Concurrent.STM
import qualified Control.Concurrent.Chan as C
import           Control.DeepSeq
import           Control.Monad (forever, forM_)
import           Data.Either (partitionEithers)
import           Data.IORef
import           Data.List (group, intercalate, partition)
import           Data.Maybe (catMaybes, fromJust, fromMaybe, mapMaybe)
import qualified Data.Map as M
import qualified Data.Set as S
import           GHC.Generics (Generic)
import           Test.QuickCheck hiding (once)

import Time
import TimeSpan

-- data Event a
--     = CLazy (Lazy (B a))
--     | Change
--         (B a)   -- ^ changes before t
--         Time    -- ^ t
--         (Lazy (Maybe a))
--                 -- ^ new value
--         (B a)   -- ^ changes after t
--     | NoChange

-- data B a = B (Lazy a) (Event a)
-- newtype E a = E (Event a)


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
data Behavior a = Step a (Event a) -- ^ initial value and value changes
    deriving (Functor, Show)
data Event a
    = NoEvents
    | Event
        (Event a)     -- ^ Values strictly before t.
        {-# UNPACK #-} !Time             -- ^ Some t
        !(Maybe a)        -- ^ Possible event at t.
        (Event a)     -- ^ Value changes strictly after t.
    deriving stock (Functor, Show, Generic)

instance Eq a => Eq (Behavior a) where
    a == b = alwaysB (==True) ((==) <$> a <*> b)

foldE :: forall a . a -> Event (a -> a) -> Event a
foldE aTop eTop = fst (go aTop eTop)
    where
    go :: a -> Event (a -> a) -> (Event a, a)
    go a NoEvents = (NoEvents, a)
    go a (Event l t fMay r) = let
        (l', a'l) = go a l
        ta' = ($ a'l) <$> fMay
        (r', a'r) = go (fromMaybe a'l ta') r
        in (Event l' t ta' r', a'r)


-- | Requires full evaluation
alwaysB :: (a -> Bool) -> Behavior a -> Bool
alwaysB f b = all f allVals
    where
    (aInit, tas) = behaviourToList b
    allVals = aInit : (snd <$> tas)

behaviourToList :: Behavior a -> (a, [(Time, a)])
behaviourToList (Step a cs) = (a, go cs)
    where
    go NoEvents = []
    go (Event left t at right) = go left ++ catMaybes [(t,) <$> at] ++ go right

-- -- | Basically a step function where you control the TimeX (inclusive) that value start.
-- listToBX :: a -> [(TimeD, a)] -> Behavior a
-- listToBX initA0 [] = (Value initA0)
-- listToBX initA0 ((initET, initEA):events) = Split (Value a) initET (listToBX initEA events)

changesFinalValue :: Event a -> Maybe a
changesFinalValue NoEvents = Nothing
changesFinalValue (Event l _ a r) = changesFinalValue r <|> a <|> changesFinalValue l

instance Applicative Behavior where
    pure a = Step a NoEvents
    (<*>) ::forall a b . Behavior (a -> b) -> Behavior a -> Behavior b
    (Step fInitTop ftop) <*> (Step aInitTop atop)
        = let (bInit, bcs, _, _, _) = go allT fInitTop ftop aInitTop atop
           in Step bInit bcs
        where
        go :: SpanExc               -- ^ Span of f
           -> (a -> b)              -- ^ `f` at the start of this span
           -> Event (a -> b)      -- ^ `f` changes within the span of f.
        --    -> SpanExc               -- ^ Span of the `a` changes. Contains the span of f
           -> a                     -- ^ `a` at the start of the `a` span
           -> Event a             -- ^ `a` changes within the span of a.
           -> (b, Event b, (a->b), a, b)
                                    -- ^ ( `b` at the start of this span
                                    --   , all b changes exactly in this span.
                                    --   , `f`,`x`,`b` at the end of this span )
        go _ f NoEvents x NoEvents = let fx = f x in (fx, NoEvents, f, x, fx)
        go _ f fcs x NoEvents = let
            fx = f x
            bcs = ($x) <$> fcs
            in (fx, bcs, fromMaybe f (changesFinalValue fcs), x, fromMaybe fx (changesFinalValue bcs))
        go fspan f NoEvents x xcs = let
            (xcs', xEnd) = crop fspan x xcs
            fx = f x
            bcs = f <$> xcs'
            in (fx, bcs, f, xEnd, fromMaybe fx (changesFinalValue bcs))
        go fspan
            f fcs@(Event fl fSplitTime ft fr)
            x xcs@(Event xl xSplitTime xt xr)

            -- Traverse xcs if possible
            | let xLeftSpace = LeftSpaceExc xSplitTime
            , xLeftSpace `contains` fspan
                = go fspan f fcs x xl
            | let xRightSpace = RightSpaceExc xSplitTime
            , xRightSpace `contains` fspan
                = let
                -- Unfortunate but true: when traversing right, we must also depend on (possibly)
                -- xl, which may contain the latest x value.
                x' = lookupB (X_JustAfter xSplitTime) (Step x xcs)
                in go fspan f fcs x' xr

            | fSplitTime == xSplitTime = let
                -- bt = fromMaybe (flEnd xlEnd) (($xlEnd) <$> ftx)
                -- btx = ($x) <$> ftx
                bt = (ft <*> xt) <|> (($x) <$> ft) <|> (f <$> xt)
                (b, bl, flEnd, xlEnd, _) = go lspan f fl x xl
                ftx = fromMaybe flEnd $ ft <|> ft
                xtx = fromMaybe xlEnd $ xt <|> xt
                (_, br, fEnd, xEnd, bEnd) = go rspan ftx fr xtx xr
                in (b, Event bl fSplitTime bt br, fEnd, xEnd, bEnd)
            | otherwise = let
                bt  = ($xlEnd) <$> ft
                (b, bl, flEnd, xlEnd, _) = go lspan f fl x xcs
                ftx = fromMaybe flEnd $ ft <|> ft
                (_, br, fEnd, xEnd, bEnd) = go rspan ftx fr x xcs
                in (b, Event bl fSplitTime bt br, fEnd, xEnd, bEnd)
            where
                (lspan, rspan) = splitSpanExcAtErr fspan fSplitTime

        crop :: SpanExc     -- ^ span to crop to
             -> d           -- ^ start value of this span
             -> Event d   -- ^ changes spanning the span and possibly more.
             -> (Event d, d)
                            -- ^ ( all d changes exactly in this span.
                            --   , `d` at the end of this span )
        crop _ bInit NoEvents = (NoEvents, bInit)
        crop tspan bInit (Event l t bt r) = case splitSpanExcAt tspan t of
            FullyLeftOfT  tspan' -> crop tspan' bInit l
            FullyRightOfT tspan' -> crop tspan' (fromMaybe bInit $ bt <|> changesFinalValue l) r
            SplitByT lspan rspan -> let
                (l', bMid) = crop lspan bInit l
                (r', bEnd) = crop rspan (fromMaybe bMid bt) r
                in (Event l' t bt r', bEnd)

-- | Basically a (immediate) step function but more convenient fr creating behaviors.
listToB :: a -> [(Time, a)] -> Behavior a
listToB initA events = step initA (listToE events)

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
lookupB t (Step aInitTop cs) = go aInitTop cs
    where
    go aInit NoEvents = aInit
    go aInit (Event left t' atM right)
        | t < toTime t'         = go aInit left
        | toTime      t' == t   = at
        | otherwise             = go at right
        where
        aL = go aInit left
        at = fromMaybe aL atM

-- | Event occurence
data Occ a = NoOcc | Occ a
    deriving stock (Eq, Show, Functor, Generic)
    deriving anyclass (Binary, NFData)

-- instance Show a => Show (Event a) where
--     show e = "Event " ++ show (eventToList e)

never :: Event a
never = NoEvents

once :: Time -> a -> Event a
once t a = listToE [(t, a)]

listToE :: [(Time, a)] -> Event a
listToE cs = go cs
    where
    go [] = NoEvents
    go ((t, a):tas) = Event NoEvents t (Just a) (go tas)

eventToList :: Event a -> [(Time, a)]
eventToList cs = go cs
    where
    go :: Event a -> [(Time, a)]
    go NoEvents = []
    go (Event l t at r) = go l ++ [(t,a) | Just a <- [at]] ++ go r

-- Immediate step.
step :: forall a . a -> Event a -> Behavior a
step aInit cs = Step aInit cs

-- | Evaluates all event occurence times.
-- Exclusive, Inclusive
-- Errors if there are overlapping time spans, or any event occurrences appear outside of the span.
listToPartialE
    :: forall a
    .  Maybe Time
    -- ^ Start time of knowlage span (excluive). Nothing means -Infinity.
    -> Maybe Time
    -- ^ Start time of knowlage span (inclusive). Nothing means Infinity.
    -> [(Time, a)]
    -- ^ Event occurences within the knowlage span (times must be strictly increasing).
    -> PartialEvent a
listToPartialE loMTop hiM xsTop
    | not (all (uncurry (<)) (zip occTs (tail occTs)))
        =  error $ "listToPartialE: time occurrences not strictly increasing: " ++ show occTs
    | let tspan = spanExc loMTop hiM
    , not (all (\t -> tspan `contains` t || Just t == hiM) occTs)
        =  error $ "listToPartialE: time occurrences not in range " ++ show (loMTop,hiM) ++ ": " ++ show occTs
    | otherwise = goNoChange loMTop xsTop
    where
    occTs = fst <$> xsTop

    goNoChange
        :: Maybe Time    -- ^ Start of NoChange exclusive (Nothing = -Inf)
        -> [(Time, a)]   -- ^ remaining event occs
        -> PartialEvent a -- ^ parts spanning from current time (inclusive) to hiM (Inc)
    goNoChange loM [] = EventPart_NoEvent (spanExc loM hiM) : goOcc []
    goNoChange loM xs@((t,_):_)
        = EventPart_NoEvent (spanExc loM (Just t)) : goOcc xs

    goOcc
        :: [(Time, a)]   -- ^ remaining event occs (current time is first event time else hiM)
        -> PartialEvent a -- ^ parts spanning from current time (inclusive) to hiM (Inc)
    goOcc [] = case hiM of
        Nothing -> []
        Just hi -> [EventPart_Event hi Nothing]
    goOcc ((t,a):xs) = EventPart_Event t (Just a) : if Just t == hiM
        then []
        else goNoChange (Just t) xs

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

sourceEvent
    :: forall a
    .  IO (PartialEvent a -> IO ()
          -- ^ Update the event
          , Event a
          )
sourceEvent = do
    -- TODO make this more efficient! We probably need to optimize for appending to the end of the known time.
    updatesChan <- C.newChan
    knowlageCoverTVar <- newTVarIO ( M.empty  -- Map from known time tspan low (exclusive) to TimeSpanExc
                                   , S.empty  -- Set of know instants
                                   )
    let updater :: PartialEvent a -> IO ()
        updater parts = do
            -- TODO can we use updatesToEvent' and observe the returned overlapping values instead of tracking them here?
            -- Check for overlap with knowlage
            hasOverlapMay <- atomically $ do
                (knownSpans, knownTimes) <- readTVar knowlageCoverTVar
                let findOverlap (EventPart_NoEvent tspan) =
                        let lo = fst (spanExcBoundaries tspan)
                            prevSpanMay = snd <$> M.lookupLE lo knownSpans
                            nextSpanMay = snd <$> M.lookupGE lo knownSpans
                            overlapStr s = "new " ++ show tspan ++ " intersects old " ++ show s
                        in if maybe False (`intersects` tspan) prevSpanMay
                            then Just (overlapStr (fromJust prevSpanMay))
                            else if maybe False (`intersects` tspan) nextSpanMay
                                then Just (overlapStr (fromJust nextSpanMay))
                                else Nothing
                    findOverlap (EventPart_Event t _) = if S.member t knownTimes
                            then Just ("existing = new = " ++ show t) else Nothing
                case mapMaybe findOverlap parts of
                    [] -> do
                        forM_ parts $ \ part -> case part of
                            -- insert new entries
                            EventPart_NoEvent tspan -> do
                                let (t,_) = spanExcBoundaries tspan
                                modifyTVar knowlageCoverTVar (\(m, s) -> (M.insert t tspan m, s))
                            EventPart_Event t _ ->
                                modifyTVar knowlageCoverTVar (\(m, s) -> (m, S.insert t s))
                        return Nothing
                    xs -> return . Just $ "Source Event: update overlaps existing knowlage: " ++ intercalate " AND " xs

            case hasOverlapMay of
                Just err -> fail err
                Nothing -> return ()
            mapM_ (C.writeChan updatesChan) parts
    updates <- C.getChanContents updatesChan
    let event = updatesToEvent updates
    return ( updater
           , event
           )

updatesToEvent :: PartialEvent a -> Event a
updatesToEvent = fst . updatesToEvent'

updatesToEvent'
    :: forall a
    .  PartialEvent a
    -> ( Event a            -- ^ The event.
       , [(SpanExc, EventPart a)]  -- ^ Event Parts that overlapped with previous event parts.
       )
updatesToEvent' updates = (occs, errCases)
    where
    (occs, _, errCases) = go allT (updates)

    go :: SpanExc
       -- ^ span of the resulting changes.
       -> PartialEvent a
       -- ^ Must all be in the span
       -> (Event a, PartialEvent a, [(SpanExc, EventPart a)])
       -- ^ Final Event for the span, unused (non-overlapping) parts, unused overlapping parts
       -- TODO Use diff lists
    go tspan allPs = case allPs of
        [] -> (NoEvents, [], [])
        (p:ps) -> if not (isInSpan tspan p)
            then let (cs, others, overlapping) = go tspan ps
                  in (cs, p:others, overlapping)
            else case p of
                EventPart_Event t at -> let
                    (lspan, rspan) = splitSpanExcAtErr tspan t
                    (r, ps' , overlaps) = go rspan ps
                    (l, ps'', overlaps') = go lspan (ps')
                    in (Event l t at r, ps'', overlaps ++ overlaps')
                EventPart_NoEvent noChangeSpan -> case tspan `difference` noChangeSpan of
                    -- (Maybe (SpanExc, Time), Maybe (Time, SpanExc))
                    (Nothing, Nothing) -> let
                        (ps', overlap) = partition (not . isInSpan noChangeSpan) ps
                        in (NoEvents, ps', (tspan,) <$> overlap)
                    (Just (lspan, tl), Nothing) -> let
                        (ps', overlapsR) = partition (not . isInSpan noChangeSpan) ps
                        (atl, ps'', overlapsTL) = siphonEvent tl ps'
                        (l, ps'2, overlapsL) = go lspan ps''
                        in ( Event l tl atl NoEvents
                           , ps'2
                           , ((noChangeSpan,) <$> overlapsR)
                                   ++ overlapsTL
                                   ++ overlapsL
                           )
                    (Nothing, Just (tr, rspan)) -> let
                        (r, ps', overlapsR) = go rspan ps
                        (atr, ps'', overlapsTR) = siphonEvent tr ps'
                        (ps'2, overlapsL) = partition (not . isInSpan noChangeSpan) ps''
                        in ( Event NoEvents tr atr r
                           , ps'2
                           , overlapsR
                                   ++ overlapsTR
                                   ++ ((noChangeSpan,) <$> overlapsL)
                           )
                    (Just (lspan, tl), Just (tr, rspan)) -> let
                        -- Right
                        (r, ps'1, overlapsR) = go rspan ps
                        (atr, ps'2, overlapsTR) = siphonEvent tr ps'1
                        (ps'3, overlapsMid) = partition (not . isInSpan noChangeSpan) ps'2
                        -- Left
                        (atl, ps'4, overlapsTL) = siphonEvent tl ps'3
                        (l, ps'5, overlapsL) = go lspan ps'4
                        in ( Event (Event l tl atl NoEvents) tr atr r
                        , ps'5
                        , overlapsR
                                ++ overlapsTR
                                ++ ((noChangeSpan,) <$> overlapsMid)
                                ++ overlapsTL
                                ++ overlapsL
                        )
      where

      isInSpan :: SpanExc -> EventPart a -> Bool
      isInSpan s (EventPart_Event t _) = s `contains` t
      isInSpan s (EventPart_NoEvent s')   = s `contains` s'

      siphonEvent :: Time -> PartialEvent a -> (Maybe a, PartialEvent a, [(SpanExc, EventPart a)])
      siphonEvent t ps' = (at, ps'', (\(p',_) -> (tspan, p')) <$> overlaps)
            where
            (at, overlaps) = case siphoned of
                                    [] -> let err = error $ "updatesToEvent: Missing change value at time " ++ show t
                                          in (err, [])
                                    (_, at'):overlaps'  -> (at', overlaps')
            (siphoned, ps'') = partitionEithers
                            [case nextP of
                                EventPart_Event t' at' | t' == t -> Left (nextP, at')
                                _ -> Right nextP
                            | nextP <- ps' ]

watchE :: NFData a => Event a -> (EventPart a -> IO ()) -> IO ThreadId
watchE changesTop callback = forkIO $ do
    let go !tspan NoEvents = callback (EventPart_NoEvent tspan)
        go !tspan (Event left !t at right) = do
            _ <- forkIO $
                (t, at) `deepseq`
                callback (EventPart_Event t at)
            let (!lspan, !rspan) = splitSpanExcAtErr tspan t
            _ <- forkIO $ go lspan left
            go rspan right
    go allT changesTop

-- | Watch a Behavior, sening data to a callback as they are evaluated.
-- A dedicated thread is created that will run the callback.
watchB
    :: forall a
    .  NFData a
    => Behavior a
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
watchLatestB :: NFData a => Behavior a -> ((TimeX, a) -> IO ()) -> IO ThreadId
watchLatestB b callback = forkIO $ do
    (_, chan) <- behaviorToChan b
    -- do forever
    let loop :: TimeX -> IO ()
        loop t = do
            part <- readChan chan
            t' <- case part of
                BehaviorPart_Init a
                    | t == X_NegInf -> t <$ callback (X_NegInf, a)
                BehaviorPart_ChangesPart (EventPart_Event t' atMay) -> case atMay of
                    (Just at)
                        | let t'' = X_Exactly t'
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
watchLatestBIORef :: NFData a => Behavior a -> IO (ThreadId, IORef (TimeX, a))
watchLatestBIORef b@(Step aInit _) = do
    ref <- newIORef (X_NegInf, aInit)
    tid <- watchLatestB b (writeIORef ref)
    return (tid, ref)

type PartialEvent a = [EventPart a]

data EventPart a
    = EventPart_Event Time (Maybe a)
    | EventPart_NoEvent SpanExc
    deriving stock (Show, Generic)
    deriving anyclass (Binary)

data BehaviorPart a
    = BehaviorPart_Init a
    | BehaviorPart_ChangesPart (EventPart a)
    deriving (Show)

behaviorToChan
    :: forall a
    .  NFData a
    => Behavior a
    -- ^ IO function to call with partial behavior value.
    -- Will always be called on it's own thread and possibly concurrently.
    -- Note the value is lazy but the times are strict
    -> IO (ThreadId, Chan (BehaviorPart a))
behaviorToChan btop = do
    updatesChan <- newChan
    tid <- forkIO $ do
        let Step a cs = btop
        _ <- forkIO $ case a of !a' -> writeChan updatesChan (BehaviorPart_Init a')
        _ <- watchE cs (writeChan updatesChan . BehaviorPart_ChangesPart)
        return ()
    return (tid, updatesChan)

--
-- QuickCheck Stuff
--

instance Arbitrary a => Arbitrary (Event a) where
    arbitrary = do
        times <- orderedList
        go (head <$> group times)
        where
        go :: [Time] -> Gen (Event a)
        go [] = return NoEvents
        go ts = do
            sizeL <- choose (0,length ts - 1)
            l <- go (take sizeL ts)
            let t = ts !! sizeL
            r <- go (drop (sizeL + 1) ts)
            at <- arbitrary
            return (Event l t at r)

instance Arbitrary a => Arbitrary (Behavior a) where
    arbitrary = Step <$> arbitrary <*> arbitrary

instance Arbitrary a => Arbitrary (Occ a) where
    arbitrary = oneof [Occ <$> arbitrary, pure NoOcc]

newtype OrderedFullEventParts a = OrderedFullEventParts [EventPart a] deriving (Show)
instance Arbitrary a => Arbitrary (OrderedFullEventParts a) where
    arbitrary = do
        occTimes :: [Time] <- increasingListOf arbitrary
        vals :: [a] <- infiniteListOf arbitrary
        let occs = zip occTimes vals
        return $ OrderedFullEventParts (listToPartialE Nothing Nothing occs)