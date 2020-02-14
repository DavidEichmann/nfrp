{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

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
    -- , toOccB
    , sampleB
    -- , step
    , watchB
    , listToB
    , Event
    , sourceEvent
    , listToE
    , eventToList
    , step
    , updatesToEvent
    ) where

import Control.Concurrent
import Control.Concurrent.STM
import qualified Control.Concurrent.Chan as C
import Control.Monad (when)
import Data.List (group, nub, partition)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M
import Test.QuickCheck

import Debug.Trace

import Time

-- TODO get this by watching a regular behavior
-- -- | like Behavior but incorporates knowlage explcitely as a Maybe.
-- newtype StrictBehavior a = StrictBehavior (Behavior (Maybe a))

data Behavior a
    = Split
        (Behavior a)     -- ^ Values up to and Including t
        TimeX            -- ^ Some t
        (Behavior a)     -- ^ Values after and Excluding t
    | Value a
    -- ^ Value in the current time span.
    deriving (Functor, Show)

instance Eq a => Eq (Behavior a) where
    a == b = alwaysB (==True) ((==) <$> a <*> b)

-- | Requires full evaluation
alwaysB :: (a -> Bool) -> Behavior a -> Bool
alwaysB f (Value a) = f a
alwaysB f (Split left _ right) = alwaysB f left && alwaysB f right

-- | Basically a (delayed) step function but more convenient.
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
        takeLeft :: TimeX -> Behavior a -> Behavior a
        takeLeft t (Split l t' r) = case compare t t' of
            EQ -> l
            LT -> takeLeft t l
            GT -> takeLeft t r
        takeLeft _ v = v

        -- Excludes t
        takeRight :: TimeX -> Behavior a -> Behavior a
        takeRight t (Split l t' r) = case compare t t' of
            EQ -> r
            LT -> takeRight t l
            GT -> takeRight t r
        takeRight _ v = v

-- TODO with our rep starting at -Inf instead of 0 we dont need to insert a new intial value!
-- This seems fishy.
delay :: Behavior a -> Behavior a
delay top = go top X_Inf
    where
    go (Split left t right) hi =
        let
        t' = delayTime t
        in if t' == hi
            then go right t'
            else Split (go left t') t' (go right t)
    go v _ = v

-- ^ No Maybe! because in this system, it will just block if the value is unknown.
sampleB :: Behavior a -> Time -> a
sampleB b t = go b
    where
    tx = X_Exactly t
    go (Value a) = a
    go (Split left t' right)
        | tx <= t'   = go left
        | otherwise  = go right

-- | Watch a Behavior, sening data to a callback as they are evaluated
watchB
    :: Behavior a
    -> ((TimeX, a, TimeX) -> IO ())
    -- ^ IO function to call with (start time inc., value, end time inclusive)
    -- Will always be called on it's own thread and possibly concurrently.
    -- Note the value is lazy but the times are strict
    -> IO ThreadId
watchB btop notifyPart = forkIO (go X_NegInf btop X_Inf)
    where
    go !lo (Value a) !hi = notifyPart (lo, a, hi)
    go !lo (Split left t right) !hi = do
        _ <- forkIO $ go lo left t
        go t right hi

-- | Event occurence
data Occ a = NoOcc | Occ a
    deriving (Eq,Show)

newtype Event a = Event { toOccB :: Behavior (Occ a) }
    deriving (Show)

-- instance Show a => Show (Event a) where
--     show e = "Event " ++ show (eventToList e)

listToE :: [(Time, a)] -> Event a
listToE [] = Event (Value NoOcc)
listToE ((t,a):es)
    = Event $ Split (Value NoOcc) (X_JustBefore t)
        (Split (Value (Occ a)) (X_Exactly t) (toOccB (listToE es)))

eventToList :: Event a -> [(Time, a)]
eventToList (Event b) = go X_NegInf X_Inf b
    where
    -- lo (exclusive)  hi (inclusive)
    go _ _ (Value NoOcc) = []
    go (X_JustBefore lo) (X_Exactly hi) (Value (Occ a))
        | lo == hi = [(lo, a)]
    go lo hi (Value (Occ _)) = error $ "eventToList: Found non-instantaneous event spanning time (exclusive, inclusive): " ++ show (lo,hi)
    go lo hi (Split l t r) = go lo t l ++ go t hi r

-- Delayed step.
step :: a -> Event a -> Behavior a
step aInit = delay . stepI aInit

-- Immediate variant of step.
stepI :: forall a . a -> Event a -> Behavior a
stepI initA0 (Event btop) = fst (go initA0 btop)
    where
    -- Remove NoOcc. If NoOcc return Nothing
    -- also return the value at the end of the span (if one exists)
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

sourceEvent :: IO ( TimeX -> Time -> a -> TimeX -> IO ()
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
    knowlageCoverTVar <- newTVarIO M.empty  -- Map from known time span low (exclusive) to that times span's hi (inclusive)
    let updater lo t a hi = do
            -- Check for overlap with knowlage
            hasOverlap <- atomically $ do
                knowlageCover <- readTVar knowlageCoverTVar
                let hi' = fromMaybe X_Inf    (snd <$> M.lookupLE lo knowlageCover)
                    lo' = fromMaybe X_NegInf (fst <$> M.lookupGE lo knowlageCover)
                if hi' < lo && hi <= lo'
                    then do
                        modifyTVar knowlageCoverTVar (M.insert lo hi) -- insert new entry
                        return False
                    else return True
            when hasOverlap (fail $ "Source Event: updated overlaps existing knowlage. (lo, t, hi) = " ++ show (lo, t, hi))
            C.writeChan updatesChan (lo, t, a, hi)
    updates <- C.getChanContents updatesChan
    let event = updatesToEvent updates
    return ( updater
           , event
           )

updatesToEvent :: [(TimeX, Time, a, TimeX)] -> Event a
updatesToEvent updates = Event (go X_NegInf X_Inf updates)
    where
    go _ _ [] = Value NoOcc -- This should never actually happen. We dont't close the chan.
    -- [minExc <= lo < tx <= hi <= maxInc]
    go minExc maxInc ((lo, t, a, hi):xs)
        | not $ minExc <= lo
                || lo < hi
                || hi <= maxInc
            = overlapErr
        | tx <= lo || tx > hi
                        = error $ "Source Event: event time is outside of knowlage span. " ++ errInfo
        | otherwise = let
            doGoLeft = minExc /= lo
            needLoTx = lo /= X_JustBefore t
            needTxHi = tx /= hi
            doGoRight = maxInc /= hi
            in case (doGoLeft, needLoTx, needTxHi, doGoRight) of
                (False, False, False, False) -> occ
                (False, False, True , False) -> Split occ   tx noOcc
                (False, True , False, False) -> Split noOcc tx occ
                (False, True , True , False) -> split2 noOcc txJB occ tx noOcc
                (False, False, False, True ) -> Split occ tx goRight
                (False, False, True , True ) -> split2 occ tx noOcc hi goRight
                (False, True , False, True ) -> split2 noOcc txJB occ tx goRight
                (False, True , True , True ) -> split3 noOcc txJB occ tx noOcc hi goRight
                (True , False, False, False) -> Split goLeft txJB occ
                (True , False, False, True ) -> split2 goLeft txJB occ tx goRight
                (True , False, True , False) -> split2 goLeft txJB occ tx noOcc
                (True , False, True , True ) -> split3 goLeft txJB occ tx noOcc hi goRight
                (True , True , False, False) -> split2 goLeft lo noOcc txJB occ
                (True , True , True , False) -> split3 goLeft lo noOcc txJB occ tx noOcc
                (True , True , False, True ) -> split3 goLeft lo noOcc txJB occ tx goRight
                (True , True , True , True ) -> split4 goLeft lo noOcc txJB occ tx noOcc hi goRight

        -- TODO we'd like to throw an error if xs has more elements and
        -- we've filled the knowlage gap. But we can't check `null xs` as
        -- that will block indefinetly. For now we just silently ignore such
        -- errors.

        where
            split2 v1 t1 v2 t2 v3 = Split v1 t1 (Split v2 t2 v3)
            split3 v1 t1 v2 t2 v3 t3 v4 = Split (Split v1 t1 v2) t2 (Split v3 t3 v4)
            split4 v1 t1 v2 t2 v3 t3 v4 t4 v5  = Split (Split v1 t1 v2) t2 (Split v3 t3 (Split v4 t4 v5))
            goLeft = go minExc lo ls
            goRight = go hi maxInc rs
            noOcc = Value NoOcc
            occ = Value (Occ a)
            tx = X_Exactly t
            txJB = X_JustBefore t
            overlapErr = error $ "Source Event: knowlage overlaps existing knowlage. " ++ errInfo
            errInfo = "(minExc, maxInc)=" ++ show (minExc, maxInc) ++ "(lo, t, hi)=" ++ show (lo, t, hi)
            -- TODO PERFORMANCE This partition is fine for a balanced tree,
            -- but for appending to the end, we'll usually end up running
            -- through the whole list, only to take of a single element (I
            -- guess this will be O(n^2) in the number of event updates :-(,
            -- I'd like to see O(log(n)) maybe you can use continuation
            -- passing style and automatically pass to the right, then the
            -- first check for the next element should be on the right most
            -- spot (Just  my rough toughts).
            (ls,rs) = partition (\ (lo',_,_,_) -> lo' < tx) xs
                -- ^ NOTE the condition is pretty loose, but is sufficient
                -- for partitioning. The go function will validate the
                -- range.

instance Arbitrary a => Arbitrary (Behavior a) where
    arbitrary = do
        times <- orderedList
        go (head <$> group times)
        where
        go :: [TimeX] -> Gen (Behavior a)
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
            return (Split l (X_JustBefore  t) (Split (Value (Occ a)) (X_Exactly t) r))