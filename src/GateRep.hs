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
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module GateRep
    ( Behavior
    , listToB
    , listToBI

    , Event
    , Occ (..)
    , listToE
    , updatesToEvent
    , updatesToEvent'
    , eventToList
    , never
    , once

    -- * Querying
    , lookupB

    -- * Combinators
    , step
    , stepI
    , leftmost

    -- * Partial Behviors/Events
    , MaybeKnown (..)
    , BehaviorPart
    , EventPart
    , listToEPart

    -- * Time Spans (TODO move to Time module)
    , Span
    , spanIncExc
    , endsOn

    -- ** Convenient Span construction.
    , allT
    , spanToExc             -- ^ Usually use this AND
    , spanFromInc           -- ^ Usually use this AND
    , spanFromIncToExc      -- ^ Usually use this

    , spanToInc
    , spanFromExc
    , spanFromExcToInc

    , spanFromIncToInc
    , spanFromExcToExc

    -- * Span operations
    , Intersect (..)
    , Difference (..)

    -- * Interfacing with the real world
    , sourceEvent
    , watchB
    , watchLatestB
    , watchLatestBIORef

    -- Internal (Exposed for testing)
    , LeftSpace
    , RightSpace
    , AllOr (..)

    -- * Quick Check
    , OrderedFullUpdates (..)
    ) where

import Control.Applicative
import Control.Concurrent
import Control.Concurrent.STM
import qualified Control.Concurrent.Chan as C
import Control.Monad (forever, forM)
import Data.IORef
import Data.List (find, foldl', group, nub, sort)
import Data.Maybe (fromJust, isJust)
import qualified Data.Map as M
import Test.QuickCheck hiding (once)

import Time


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


data Behavior a
    = Split
        (Behavior a)     -- ^ Values up to and Excluding t. Yes! Excluding is correct!
        TimeD            -- ^ Some t
        (Behavior a)     -- ^ Values after and Including t
    | Value a
    -- ^ Value in the current time tspan.
    deriving (Functor, Show)

instance Eq a => Eq (Behavior a) where
    a == b = alwaysB (==True) ((==) <$> a <*> b)

-- | Requires full evaluation
alwaysB :: (a -> Bool) -> Behavior a -> Bool
alwaysB f (Value a) = f a
alwaysB f (Split left _ right) = alwaysB f left && alwaysB f right

-- -- | Basically a step function where you control the TimeX (inclusive) that value start.
-- listToBX :: a -> [(TimeD, a)] -> Behavior a
-- listToBX initA0 [] = (Value initA0)
-- listToBX initA0 ((initET, initEA):events) = Split (Value a) initET (listToBX initEA events)

-- | Basically a (immediate) step function but more convenient fr creating behaviors.
listToBI :: a -> [(Time, a)] -> Behavior a
listToBI initA events = stepI initA (listToE events)

-- | Basically a (delayed) step function but more convenient fr creating behaviors.
listToB :: a -> [(Time, a)] -> Behavior a
listToB initA events = step initA (listToE events)

instance Applicative Behavior where
    pure = Value
    ftop <*> xtop = go ftop xtop
        where
        go :: Behavior (x -> y) -> Behavior x -> Behavior y
        go (Value f) (Value x) = Value (f x)
        go fs (Value x)
            = ($x) <$> fs
        go (Value f) xs
            = f <$> xs
        go (Split fL fT fR) (Split xL xT xR) = case compare fT xT of
            EQ -> Split (fL <*> xL) fT (fR <*> xR)
            LT -> Split (fL <*> takeLeft fT xL)
                        fT
                        (Split (takeLeft xT fR <*> takeRight xT xL)
                               xT
                               (takeRight xT fR <*> xR)
                        )
            GT -> Split (takeLeft fT fL <*> xL)
                        xT
                        (Split (takeRight xT fR <*> takeLeft xT xL)
                               fT
                               (fR <*> takeRight xT xR)
                        )

        -- Includes t
        takeLeft :: TimeD -> Behavior a -> Behavior a
        takeLeft t (Split l t' r) = case compare t t' of
            EQ -> l
            LT -> takeLeft t l
            GT -> takeLeft t r
        takeLeft _ v = v

        -- Excludes t
        takeRight :: TimeD -> Behavior a -> Behavior a
        takeRight t (Split l t' r) = case compare t t' of
            EQ -> r
            LT -> takeRight t l
            GT -> takeRight t r
        takeRight _ v = v

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

--
-- Time Span stuff
--

data AllOr a
    = All   -- ^ All of time [-Inf, Inf]
    | Or a  -- ^ Just that a.
    deriving (Show) -- NOT Ord

-- Half spaces
newtype LeftSpace  = LeftSpace  TimeD   -- ^ [[ LeftSpace  t' ]] = { t | t <  t' }
    deriving (Eq,Ord)
newtype RightSpace = RightSpace TimeD   -- ^ [[ RightSpace t' ]] = { t | t >= t' }
    deriving (Eq,Ord)

instance Show LeftSpace where
    show (LeftSpace t) = "←" ++ show t ++ "○"
instance Show RightSpace where
    show (RightSpace t) = "●" ++ show t ++ "→"

deriving instance Eq (AllOr LeftSpace)
deriving instance Eq (AllOr RightSpace)

-- [[ Span l r ]] = l `intersect` r
data Span
    = Span
        (AllOr RightSpace) -- ^ Time span left  bound Inclusive. All == Inclusive -Inf
        (AllOr LeftSpace)  -- ^ Time span right bound Exclusive. All == !Inclusive! Inf
    deriving (Eq) -- NOT Ord

instance Show Span where
    show (Span allOrR allOrL) = "Span [" ++ rt  ++ " " ++ lt ++ "]"
        where
        rt = case allOrR of
            All -> "←"
            Or r -> show r
        lt = case allOrL of
            All -> "→"
            Or l -> show l

-- Inclusive start Exclusive end span.
spanIncExc :: Maybe TimeD -> Maybe TimeD -> Span
spanIncExc lo hi
    = case spanIncExcMaybe lo hi of
        Nothing -> error "spanIncExc: lo >= hi"
        Just x -> x

-- Inclusive start Exclusive end span.
-- Nothing if the input times are not strictly increasing.
spanIncExcMaybe :: Maybe TimeD -> Maybe TimeD -> Maybe Span
spanIncExcMaybe lo hi = (maybe All (Or . RightSpace) lo) `intersect`
                        (maybe All (Or . LeftSpace) hi)

-- More convenient span creating functions
spanToInc :: Time -> Span
spanToInc hi= spanIncExc Nothing (Just $ delay $ toTime hi)
spanToExc :: Time -> Span
spanToExc hi= spanIncExc Nothing (Just $ toTime hi)
spanFromInc :: Time -> Span
spanFromInc lo = spanIncExc (Just $ toTime lo) Nothing
spanFromExc :: Time -> Span
spanFromExc lo = spanIncExc (Just $ delay $ toTime lo) Nothing
spanFromIncToExc :: Time -> Time -> Span
spanFromIncToExc lo hi = spanIncExc (Just $ toTime lo) (Just $ toTime hi)
spanFromIncToInc :: Time -> Time -> Span
spanFromIncToInc lo hi = spanIncExc (Just $ toTime lo) (Just $ delay $ toTime hi)
spanFromExcToExc :: Time -> Time -> Span
spanFromExcToExc lo hi = spanIncExc (Just $ delay $ toTime lo) (Just $ toTime hi)
spanFromExcToInc :: Time -> Time -> Span
spanFromExcToInc lo hi = spanIncExc (Just $ delay $ toTime lo) (Just $ delay $ toTime hi)

class Intersect a b c | a b -> c where
    intersect :: a -> b -> c

instance Intersect LeftSpace RightSpace (Maybe Span) where intersect = flip intersect
instance Intersect RightSpace LeftSpace (Maybe Span) where
    intersect r@(RightSpace lo) l@(LeftSpace hi)
        | lo < hi = Just (Span (Or r) (Or l))
        | otherwise = Nothing
instance Intersect Span LeftSpace (Maybe Span) where intersect = flip intersect
instance Intersect LeftSpace Span (Maybe Span) where
    intersect ls (Span r l) = r `intersect` (l `intersect` ls)
instance Intersect Span RightSpace (Maybe Span) where intersect = flip intersect
instance Intersect RightSpace Span (Maybe Span) where
    intersect rs (Span r l) = l `intersect` (r `intersect` rs)
instance Intersect Span Span (Maybe Span) where
    intersect s (Span r l) = intersect l =<< (r `intersect` s)
instance Intersect (AllOr LeftSpace ) LeftSpace  LeftSpace    where intersect = allOrIntersect
instance Intersect (AllOr RightSpace) RightSpace RightSpace   where intersect = allOrIntersect
instance Intersect (AllOr RightSpace) Span       (Maybe Span) where intersect = allOrIntersectMaybe
instance Intersect (AllOr LeftSpace ) Span       (Maybe Span) where intersect = allOrIntersectMaybe
instance Intersect RightSpace RightSpace RightSpace where
    intersect (RightSpace a) (RightSpace b) = RightSpace (max a b)
instance Intersect LeftSpace LeftSpace LeftSpace where
    intersect (LeftSpace a) (LeftSpace b) = LeftSpace (min a b)
instance Intersect (AllOr LeftSpace ) (AllOr RightSpace) (Maybe Span) where intersect = flip intersect
instance Intersect (AllOr RightSpace) (AllOr LeftSpace)  (Maybe Span) where
    intersect (Or rs) (Or ls) = rs `intersect` ls
    intersect allOrRs allOrLs = Just (Span allOrRs allOrLs)
instance Intersect (AllOr LeftSpace) RightSpace (Maybe Span) where intersect = flip intersect
instance Intersect RightSpace (AllOr LeftSpace) (Maybe Span) where
    intersect rs (Or ls) = rs `intersect` ls
    intersect rs All = Just (Span (Or rs) All)
instance Intersect LeftSpace (AllOr RightSpace) (Maybe Span) where intersect = flip intersect
instance Intersect (AllOr RightSpace) LeftSpace (Maybe Span) where
    intersect (Or rs) ls = rs `intersect` ls
    intersect All ls = Just (Span All (Or ls))

allOrIntersectMaybe :: Intersect a b (Maybe b) => AllOr a -> b -> Maybe b
allOrIntersectMaybe All b = Just b
allOrIntersectMaybe (Or a) b = a `intersect` b

allOrIntersect :: Intersect a b b => AllOr a -> b -> b
allOrIntersect All b = b
allOrIntersect (Or a) b = a `intersect` b

-- allOrIntersect :: Intersect a b (Maybe c) => AllOr a -> b -> b
-- allOrIntersect All b = b
-- allOrIntersect (Or a) b = a `intersect` b


-- a `difference` b == a `intersect` (invert b)
class Difference a b c | a b -> c where
    difference :: a -> b -> c
instance Difference LeftSpace LeftSpace (Maybe Span) where
    difference lsa (LeftSpace b) = lsa `intersect` RightSpace b
instance Difference RightSpace RightSpace (Maybe Span) where
    difference rsa (RightSpace b) = rsa `intersect` LeftSpace b
instance Difference Span Span (Maybe Span, Maybe Span) where
    difference a (Span rs ls) = (a `difference` rs, a `difference` ls)
instance Difference Span LeftSpace (Maybe Span) where
    difference s (LeftSpace b) = s `intersect` (RightSpace b)
instance Difference Span RightSpace (Maybe Span) where
    difference s (RightSpace b) = s `intersect` (LeftSpace b)
instance Difference a b (Maybe c) => Difference a (AllOr b) (Maybe c) where
    difference _ All = Nothing
    difference a (Or b) = a `difference` b

class NeverAll a
instance NeverAll LeftSpace
instance NeverAll RightSpace

class Contains a b where
    contains :: a -> b -> Bool

instance Contains LeftSpace TimeD where
    contains (LeftSpace a) t = t < a
instance Contains RightSpace TimeD where
    contains (RightSpace a) t = t >= a
instance Contains LeftSpace Time where
    contains ls t = ls `contains` D_Exactly t
instance Contains RightSpace Time where
    contains rs t = rs `contains` D_Exactly t
instance Contains Span Time where
    contains (Span rs ls) t = ls `contains` t && rs `contains` t
instance Contains LeftSpace LeftSpace where
    contains (LeftSpace a) (LeftSpace b) = a >= b
instance Contains RightSpace RightSpace where
    contains (RightSpace a) (RightSpace b) = a <= b
instance Contains LeftSpace Span where
    contains ls (Span _ allOrLs) = ls `contains` allOrLs
instance Contains RightSpace Span where
    contains rs (Span allOrRs _) = rs `contains` allOrRs
instance Contains Span Span where
    contains (Span r l) s = r `contains` s && l `contains` s
instance (Contains a b, IsAllT a) => Contains a (AllOr b) where
    contains a All    = isAllT a
    contains a (Or b) = a `contains` b
instance (Contains a b, IsAllT a) => Contains (AllOr a) b where
    contains All _ = True
    contains (Or a) b = a `contains` b

intersects :: Intersect a b (Maybe c) => a -> b -> Bool
intersects a b = isJust (a `intersect` b)

-- | Covering all of time
class AllT a where allT :: a
instance AllT Span where allT = Span All All
instance AllT (AllOr a) where allT = All

class IsAllT a where isAllT :: a -> Bool
instance IsAllT LeftSpace where isAllT _ = False
instance IsAllT RightSpace where isAllT _ = False


-- | If the left arg ends exactly on the start of the right arg, return the
-- joined span and the time at which they are joined (such that splitting on
-- that time will give the original spans).
endsOn :: Span -> Span -> Maybe (Span, TimeD)
endsOn (Span allOrRs (Or (LeftSpace hi))) (Span (Or (RightSpace lo)) allOrLs)
    | hi == lo  = Just (Span allOrRs allOrLs, lo)
endsOn _ _ = Nothing

instantaneous :: Span -> Maybe Time
instantaneous (Span (Or (RightSpace (D_Exactly t))) (Or (LeftSpace (D_JustAfter t'))))
    | t == t' = Just t
instantaneous _ = Nothing

splitSpanAt :: Span -> TimeD -> (Maybe Span, Maybe Span)
splitSpanAt tspan t = (tspan `intersect` LeftSpace t, tspan `intersect` RightSpace t)

splitSpanAtErr :: Span -> TimeD -> String -> (Span, Span)
splitSpanAtErr tspan t err = case splitSpanAt tspan t of
    (Just lspan, Just rspan) -> (lspan, rspan)
    _ -> error $ err ++ ": splitSpanAtErr: Found a (Split _ (" ++ show t ++ ") _) but are in span: " ++ show tspan

spanToIncInc :: Span -> (TimeX, TimeX)
spanToIncInc (Span r l) = (lo, hi)
    where
    lo = case r of
            All -> X_NegInf
            (Or (RightSpace loD)) -> toTime loD
    hi = case l of
            All -> X_Inf
            (Or (LeftSpace hiD)) -> case hiD of
                D_Exactly t -> X_JustBefore t
                D_JustAfter t -> X_Exactly t



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

instance Arbitrary Span where
    arbitrary = arbitrary `suchThatMap` (uncurry spanIncExcMaybe)

instance Arbitrary LeftSpace where arbitrary = LeftSpace <$> arbitrary
instance Arbitrary RightSpace where arbitrary = RightSpace <$> arbitrary
instance Arbitrary a => Arbitrary (AllOr a) where
    arbitrary = frequency [(1, return All), (15, Or <$> arbitrary)]

-- | Spans that cover all time.
newtype OrderedFullSpans = OrderedFullSpans [Span]
instance Arbitrary OrderedFullSpans where
    arbitrary = do
        spanTimeEdgesT :: [Time] <- fmap head . group <$> orderedList
        spanTimeEdgesBools :: [Bool] <- infiniteList
        let spanTimeEdges = zip spanTimeEdgesT spanTimeEdgesBools
        return $ OrderedFullSpans $ case spanTimeEdges of
                    [] -> [allT]
                    _ -> (let (t, notHiInc) = head spanTimeEdges in spanIncExc Nothing (Just $ if not notHiInc then D_JustAfter t else D_Exactly t))
                        : (zipWith
                            (\ (lo, loInc) (hi, notHiInc) -> spanIncExc
                                                                (Just $ if loInc        then D_Exactly lo else D_JustAfter lo)
                                                                (Just $ if not notHiInc then D_JustAfter hi else D_Exactly hi)
                            )
                            spanTimeEdges
                            (tail spanTimeEdges)
                          ) ++ [let (t, loInc) = last spanTimeEdges in spanIncExc (Just (if loInc then D_Exactly t else D_JustAfter t)) Nothing]

arbitraryTimeDInSpan :: Span -> Gen TimeD
arbitraryTimeDInSpan (Span All All) = arbitrary
arbitraryTimeDInSpan (Span (Or (RightSpace t)) All)
    = frequency [ (1, return t)
                , (5, sized $ \n -> choose (t, t+(fromIntegral n)))
                ]
arbitraryTimeDInSpan (Span All (Or (LeftSpace t)))
    = sized $ \n -> choose (t-(fromIntegral n), t)
arbitraryTimeDInSpan (Span (Or (RightSpace lo)) (Or (LeftSpace hi)))
    = frequency [ (1, return lo)
                , (5, choose (lo,hi))
                ]

arbitraryTimeInSpan :: Span -> Gen Time
arbitraryTimeInSpan s = arbitraryTimeDInSpan s `suchThatMap` (\td -> let
    t = closestTime td
    in if s `contains` t then Just t else Nothing)


increasingListOf :: Ord a => Gen a -> Gen [a]
increasingListOf xs = fmap head . group . sort <$> listOf xs

newtype OrderedFullUpdates a = OrderedFullUpdates [(Span, [(Time, a)])] deriving (Show)
instance Arbitrary a => Arbitrary (OrderedFullUpdates a) where
    arbitrary = do
        OrderedFullSpans spans <- arbitrary
        updates <- forM spans $ \ tspan -> do
                    eventTimes <- increasingListOf (arbitraryTimeInSpan tspan)
                    values <- infiniteList
                    return $ (tspan, zip eventTimes values)
        return $ OrderedFullUpdates updates