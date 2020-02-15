{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

{-# LANGUAGE BangPatterns #-}
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
    ( Behavior
    -- , unEvent
    , sampleB
    -- , step
    -- , watchB
    , listToB
    , listToBI
    , Event
    -- , sourceEvent
    , listToE
    , eventToList
    , step
    , updatesToEvent

    , MaybeKnown (..)
    , BehaviorPart
    , EventPart
    ) where

import Control.Concurrent
import Control.Concurrent.STM
import qualified Control.Concurrent.Chan as C
import Control.Monad (when)
import Data.List (group, nub, partition)
import Data.Maybe (fromJust, fromMaybe)
import qualified Data.Map as M
import Test.QuickCheck

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
-- In Split, use TimeDI only, and make it the *inclusive* start time of right
-- and the *exclusive* start time of left. Still Use TimeX to track the
-- inclusive-inclusive min-max range of a value.


data Behavior a
    = Split
        (Behavior a)     -- ^ Values up to and Excluding t. Yes! Excluding is correct!
        TimeDI           -- ^ Some t
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
-- listToBX :: a -> [(TimeDI, a)] -> Behavior a
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
        takeLeft :: TimeDI -> Behavior a -> Behavior a
        takeLeft t (Split l t' r) = case compare t t' of
            EQ -> l
            LT -> takeLeft t l
            GT -> takeLeft t r
        takeLeft _ v = v

        -- Excludes t
        takeRight :: TimeDI -> Behavior a -> Behavior a
        takeRight t (Split l t' r) = case compare t t' of
            EQ -> r
            LT -> takeRight t l
            GT -> takeRight t r
        takeRight _ v = v
-- TODO with our rep starting at -Inf instead of 0 we dont need to insert a new intial value!
-- This seems fishy.
delay :: Behavior a -> Behavior a
delay top = go top DI_Inf
    where
    go (Split left t right) hi =
        let
        t' = delayTime t
        -- If there is already a next value at the delayed time, then discard the right value.
        in if t' == hi
            then go left t'
            else Split (go left t') t' (go right hi)
    go v _ = v

-- ^ No Maybe! because in this system, it will just block if the value is unknown.
sampleB :: Behavior a -> Time -> a
sampleB b t = go b
    where
    tdi = DI_Exactly t
    go (Value a) = a
    go (Split left t' right)
        | tdi < t'   = go left
        | otherwise  = go right

-- -- | Watch a Behavior, sening data to a callback as they are evaluated
-- watchB
--     :: Behavior a
--     -> (BehaviorPart a -> IO ())
--     -- ^ IO function to call with partial behavior value.
--     -- Will always be called on it's own thread and possibly concurrently.
--     -- Note the value is lazy but the times are strict
--     -> IO ThreadId
-- watchB btop notifyPart = forkIO (go X_NegInf btop X_Inf)
--     where
--     -- lo is exclusive and hi is inclusive of the current time tspan.
--     go !lo (Value a) !hi = notifyPart (listToBX Unknown [(delayTime lo, Known a), (hi, Unknown)])
--     go !lo (Split left t right) !hi = do
--         _ <- forkIO $ go lo left t
--         go t right hi

-- | Event occurence
data Occ a = NoOcc | Occ a
    deriving (Eq,Show)

newtype Event a = Event { unEvent :: Behavior (Occ a) }
    deriving (Show)

-- instance Show a => Show (Event a) where
--     show e = "Event " ++ show (eventToList e)

listToE :: [(Time, a)] -> Event a
listToE [] = Event (Value NoOcc)
listToE ((t,a):es)
    = Event $ Split (Value NoOcc) (DI_Exactly t)
        (Split (Value (Occ a)) (DI_JustAfter t) (unEvent (listToE es)))

eventToList :: Event a -> [(Time, a)]
eventToList (Event b) = go spanInf b
    where
    go :: IncSpan -> Behavior (Occ a) -> [(Time, a)]
    go _ (Value NoOcc) = []
    go (lo, hi) (Value (Occ a))
        | lo == hi = case lo of
            X_Exactly lo' -> [(lo', a)]
            _ -> error $ "eventToList: found a non-DI_Exactly occurence at: " ++ show lo
        | otherwise = error $ "eventToList: Found non-instantaneous event spanning time (exclusive, inclusive): " ++ show (lo,hi)
    go tspan (Split l t r) = go (tspan |<-| t) l ++ go (t |->| tspan) r

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


--
-- Explicitly partial versions of Behavior/Event
--

data MaybeKnown a = Unknown | Known a
type BehaviorPart a = Behavior (MaybeKnown a)
newtype EventPart a = EventPart { unEventPart :: BehaviorPart (Occ a) }

eventPart :: [(IncSpan, [(Time, a)])] -> EventPart a
eventPart spans =

knownSpansE :: EventPart a -> [(IncSpan, Event a)]
knownSpansE (EventPart b) = fmap Event <$> knownSpansB b

knownSpansB :: BehaviorPart a -> [(IncSpan, Behavior a)]
knownSpansB btop = go spanInf btop
    where
    -- This is very similar to eventToList
    go :: IncSpan -> Behavior (MaybeKnown a) -> [(IncSpan, Behavior a)]
    go _     (Value Unknown) = []
    go tspan (Value (Known a)) = [(tspan, Value a)]
    go tspan (Split l t r) = let
        spansL = go (tspan |<-| t) l
        spansR = go (t |->| tspan) r
        in if null spansL
            then spansR
            else if null spansR
                then []
                else let
                    ((loL,hiL),lastLB) = last spansL
                    ((loR,hiR),headRB) = head spansR
                    in if  hiL `neighbotTimes` loR
                        -- stick spans together
                        then init spansL ++ [((loL,hiR), Split lastLB (loSpanToTimeErr loR) headRB)] ++ tail spansR
                        else spansL ++ spansR
--
-- IO stuff
--

{-
chanToEvent :: Chan (EventPart a) -> IO (Event a)
chanToEvent inputChan = do
    updates <- C.getChanContents inputChan
    return (updatesToEvent updates)

eventToChan :: Event a -> IO (Chan (EventPart a))
eventToChan e = do
    let b = unEvent e
    _watchB b

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
            -- Check for overlap with knowlage
            partSpans :: [IncSpan] <- _knownSpansE part
            hasOverlapMay <- atomically $ do
                let loop [] = do
                            -- insert new entries
                            let partSpansMap = M.fromList partSpans
                            modifyTVar knowlageCoverTVar (M.union partSpansMap)
                            return Nothing
                    loop (tspan@(lo,_):xs) = do
                        knowlageCover <- readTVar knowlageCoverTVar
                        let prevSpanMay = M.lookupLE lo knowlageCover
                            nextSpanMay = M.lookupGE lo knowlageCover
                        if maybe False (spansIntersect tspan) prevSpanMay
                            then return (Just (tspan, fromJust prevSpanMay))
                            else if maybe False (spansIntersect tspan) nextSpanMay
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

-}

updatesToEvent :: [EventPart a] -> Event a
updatesToEvent updates = Event (go spanInf updates')
    where
    updates' = [ ks
                | update <- updates
                , ks <- knownSpansE update
                ]

    go :: IncSpan -> [(IncSpan, Event a)] -> Behavior (Occ a)
    go _ [] = Value NoOcc -- This should never actually happen. We dont't close the chan.
    go tspanOut@(loOut, hiOut) ((tspanIn@(loIn, hiIn), (Event b)):xs)
        | not (tspanOut `spanContains` tspanIn)
            = error "updatesToEvent: overlapping knowlage"
        | otherwise = case (loOut == loIn, hiIn == hiOut) of
            (True , True ) -> b
            (True , False) -> Split b hiSplitTime goRight
            (False, True ) -> Split goLeft loSplitTime b
            (False, False) -> Split goLeft loSplitTime (Split b hiSplitTime goRight)
        where
        -- assumes b is left child
        hiSplitTime = hiSpanToExcTime hiIn
        goRight = go (hiSplitTime |->| tspanOut) rs
        -- assumes b is right child
        loSplitTime = loSpanToTimeErr loIn
        goLeft = go (tspanOut |<-| loSplitTime) ls

        -- TODO PERFORMANCE This partition is fine for a balanced tree,
        -- but for appending to the end, we'll usually end up running
        -- through the whole list, only to take of a single element (I
        -- guess this will be O(n^2) in the number of event updates :-(,
        -- I'd like to see O(log(n)) maybe you can use continuation
        -- passing style and automatically pass to the right, then the
        -- first check for the next element should be on the right most
        -- spot (Just  my rough toughts).
        (ls,rs) = partition (\ ((lo',_),_) -> lo' < loIn) xs
            -- ^ NOTE the condition is pretty loose, but is sufficient
            -- for partitioning. The go function will validate the
            -- range.

    -- go _ [] = Value NoOcc -- This should never actually happen. We dont't close the chan.
    -- -- [minExc <= lo < tx <= hi <= maxInc]
    -- go (minExc, maxInc) ((lo, t, a, hi):xs) -- TODO fix!
    --     | not $ minExc <= lo
    --             || lo < hi
    --             || hi <= maxInc
    --         = overlapErr
    --     | tx <= lo || tx > hi
    --                     = error $ "Source Event: event time is outside of knowlage tspan. " ++ errInfo
    --     | otherwise = let
    --         doGoLeft = minExc /= lo
    --         needLoTx = lo /= X_JustBefore t
    --         needTxHi = tx /= hi
    --         doGoRight = maxInc /= hi
    --         in case (doGoLeft, needLoTx, needTxHi, doGoRight) of
    --             (False, False, False, False) -> occ
    --             (False, False, True , False) -> Split occ   tx noOcc
    --             (False, True , False, False) -> Split noOcc tx occ
    --             (False, True , True , False) -> split2 noOcc txJB occ tx noOcc
    --             (False, False, False, True ) -> Split occ tx goRight
    --             (False, False, True , True ) -> split2 occ tx noOcc hi goRight
    --             (False, True , False, True ) -> split2 noOcc txJB occ tx goRight
    --             (False, True , True , True ) -> split3 noOcc txJB occ tx noOcc hi goRight
    --             (True , False, False, False) -> Split goLeft txJB occ
    --             (True , False, False, True ) -> split2 goLeft txJB occ tx goRight
    --             (True , False, True , False) -> split2 goLeft txJB occ tx noOcc
    --             (True , False, True , True ) -> split3 goLeft txJB occ tx noOcc hi goRight
    --             (True , True , False, False) -> split2 goLeft lo noOcc txJB occ
    --             (True , True , True , False) -> split3 goLeft lo noOcc txJB occ tx noOcc
    --             (True , True , False, True ) -> split3 goLeft lo noOcc txJB occ tx goRight
    --             (True , True , True , True ) -> split4 goLeft lo noOcc txJB occ tx noOcc hi goRight

    --     -- TODO we'd like to throw an error if xs has more elements and
    --     -- we've filled the knowlage gap. But we can't check `null xs` as
    --     -- that will block indefinetly. For now we just silently ignore such
    --     -- errors.

    --     where
    --         split2 v1 t1 v2 t2 v3 = Split v1 t1 (Split v2 t2 v3)
    --         split3 v1 t1 v2 t2 v3 t3 v4 = Split (Split v1 t1 v2) t2 (Split v3 t3 v4)
    --         split4 v1 t1 v2 t2 v3 t3 v4 t4 v5  = Split (Split v1 t1 v2) t2 (Split v3 t3 (Split v4 t4 v5))
    --         goLeft = go minExc lo ls
    --         goRight = go hi maxInc rs
    --         noOcc = Value NoOcc
    --         occ = Value (Occ a)
    --         tx = X_Exactly t
    --         txJB = X_JustBefore t
    --         overlapErr = error $ "Source Event: knowlage overlaps existing knowlage. " ++ errInfo
    --         errInfo = "(minExc, maxInc)=" ++ show (minExc, maxInc) ++ "(lo, t, hi)=" ++ show (lo, t, hi)

--
-- QuickCheck Stuff
--

instance Arbitrary a => Arbitrary (Behavior a) where
    arbitrary = do
        times <- orderedList
        go (head <$> group times)
        where
        go :: [TimeDI] -> Gen (Behavior a)
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
            return (Split l (DI_Exactly t) (Split (Value (Occ a)) (DI_JustAfter t) r))


--
-- Time Span stuff
--


type IncSpan = (TimeX, TimeX) -- inclusive-inclusive min-max time tspan.
type LeftBoundary = TimeDI -- The left boundary of a time tspan (Inclusive)
type RightBoundary = TimeDI -- The Right boundary of a time tspan (Exclusive)

-- |  If the tspan is within the halfspace defined by a Left boundary (extending right |->)
intersectsLeftB :: IncSpan -> LeftBoundary -> Bool
intersectsLeftB (_, hi) t = hi >= toTime t

-- |  If the tspan is within the halfspace defined by a Right boundary (extending left <-|)
intersectsRightB :: IncSpan -> RightBoundary -> Bool
intersectsRightB (lo, _) t = lo <= justBeforeIshDI t

justBeforeIshDI :: TimeDI -> TimeX
justBeforeIshDI (DI_Exactly t) = X_JustBefore t
justBeforeIshDI (DI_JustAfter t) = X_Exactly t
justBeforeIshDI DI_Inf = X_Inf

-- Crop the left of a tspan using the left boundary (inclusive).
(|->|) :: LeftBoundary -> IncSpan -> IncSpan
(|->|) tl'_di (tl, tr)
    | not (tl <= tl' && tl' <= tr)
    = error $ "trying to crop but not in range: "
                ++ show tl'_di
                ++ " |->| "
                ++ show (tl, tr)
    | otherwise =  (tl', tr)
    where
    tl' = toTime tl'_di

-- Crop the right of a tspan using the right boundary (exclusive).
(|<-|) :: IncSpan -> RightBoundary -> IncSpan
(|<-|) (tl, tr) tr'_di
    | not (tl <= tr' && tr' <= tr)
    = error $ "trying to crop but not in range: "
                ++ show tr'_di
                ++ " |<-| "
                ++ show (tl, tr)
    | otherwise =  (tl, tr')
    where
    tr' = justBeforeIshDI tr'_di

-- Crop to the given times. Left of the tspan is just the start of the tspan value.
-- right of the tspan is just the end of the tspan value.
crop :: IncSpan -> Behavior a -> Behavior a
crop _ v@(Value _) = v
crop tspan (Split left t right) = case (tspan `intersectsRightB` t, tspan `intersectsLeftB` t) of
    (True, True) -> Split left' t right'
    (True, False) -> left'
    (False, True) -> right'
    (False, False) -> error "crop: Impossible!"
    where
    left'  = crop (tspan |<-| t) left
    right' = crop (t |->| tspan) right

spanInf :: IncSpan
spanInf = (X_NegInf, X_Inf)

spansIntersect :: IncSpan -> IncSpan -> Bool
spansIntersect (lo1, hi1) (lo2, hi2) = not (hi1 < lo2 || hi2 < lo1)

spanContains :: IncSpan -> IncSpan -> Bool
spanContains (lo1, hi1) (lo2, hi2) = lo1 <= lo2 && hi2 <= hi2



loSpanToTimeErr :: TimeX -> TimeDI
loSpanToTimeErr = toTimeErr err
    where
    err = "Lowwer bound on IncSpan is only set to TimeDI's from Splits"
        ++ " ans considering it's on the right, and knowlage exists on the right,"
        ++ " we know it's not the intial -Inf, so it must be Exactly or JustAfter."
        ++ " Hence we can safely convert to TimeDI"

-- | only call this on a IncSpan's hi value.
-- Returns the TimeDI of the parent Split assuming this is the left child.
hiSpanToExcTime :: TimeX -> TimeDI
hiSpanToExcTime (X_JustBefore t) = (DI_Exactly t)
hiSpanToExcTime (X_Exactly t) = (DI_JustAfter t)
hiSpanToExcTime X_Inf = DI_Inf
hiSpanToExcTime x = error $ "hiSpanToExcTime: unexpected hi IncSpan time: " ++ show x