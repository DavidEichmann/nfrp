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
    , step
    , eventToList
    ) where

import Control.Concurrent
import qualified Control.Concurrent.Chan as C
import Data.List (nub, partition)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M
import System.IO.Unsafe (unsafeInterleaveIO)
import Test.QuickCheck

import Time

-- TODO get this by watching a regular behavior
-- -- | like Behavior but incorporates knowlage explcitely as a Maybe.
-- newtype StrictBehavior a = StrictBehavior (Behavior (Maybe a))

data Behavior a
    = Split
        (Behavior a)     -- ^ Values up to t
        Time             -- ^ Some t
        Bool             -- ^ True if t belongs to left else right
        (Behavior a)     -- ^ Values after t
    | Value a
    -- ^ Value in the current time span.
    deriving (Functor, Show)

instance Eq a => Eq (Behavior a) where
    a == b = alwaysB (==True) ((==) <$> a <*> b)

-- | Requires full evaluation
alwaysB :: (a -> Bool) -> Behavior a -> Bool
alwaysB f (Value a) = f a
alwaysB f (Split left _ _ right) = alwaysB f left && alwaysB f right

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
        go f@(Split fL fT fTI fR) x@(Split xL xT xTI xR)
            | fT == xT && fTI == xTI
                = Split (fL <*> xL) fT fTI (fR <*> xR)
            | otherwise
                = let
                    leftLoTX  = (min fTL xTL)
                    rightLoTX = (min fTR xTR)
                    (loT, loTInc) = leftTimeXToTInc leftLoTX
                    leftHiTX  = (max fTL xTL)
                    rightHiTX = (max fTR xTR)
                    (hiT, hiTInc) = leftTimeXToTInc leftHiTX
                    lo  = go (openCrop X_NegInf  leftLoTX fL)
                             (openCrop X_NegInf  leftLoTX xL)
                    mid = go (openCrop rightLoTX leftHiTX f )
                             (openCrop rightLoTX leftHiTX x )
                    hi  = go (openCrop rightHiTX X_Inf    fR)
                             (openCrop rightHiTX X_Inf    xR)
                in Split lo loT loTInc (Split mid hiT hiTInc hi)
            where
            (fTL, fTR) = toLeftRightTimeX fT fTI
            (xTL, xTR) = toLeftRightTimeX xT xTI

        -- | given t and isLeftIncl, get the left end time and right start itme.
        toLeftRightTimeX :: Time -> Bool -> (TimeX,TimeX)
        toLeftRightTimeX t inc = if inc
                                    then (X_Exactly    t, X_JustAfter t)
                                    else (X_JustBefore t, X_Exactly   t)

        -- | given t and isLeftIncl, get the left end time and right start itme.
        leftTimeXToTInc  (X_Exactly    t) = (t, True)
        leftTimeXToTInc  (X_JustBefore t) = (t, False)
        leftTimeXToTInc  _                = error "leftTimeXToTInc: unexpected."

        -- rightTimeXToTInc (X_Exactly    t) = (t, False)
        -- rightTimeXToTInc (X_JustAfter  t) = (t, True)
        -- rightTimeXToTInc _                = error "leftTimeXToTInc: unexpected."

        -- Crop to the given time interval. the interval boundaries span a Value,
        -- then the value is left "open" i.e NOT Split on the boundary.
        -- Returns nothing if there is no info.
        openCrop :: TimeX -> TimeX -> Behavior a -> Behavior a
        openCrop loT hiT b = openCrop' b
            where
            openCrop' (Value a) = Value a -- Keep Open
            openCrop' (Split left t inc right)
                -- Completely to the left
                | hiT == leftT = left
                | hiT <  leftT = openCrop' left
                -- Completely to the Right
                | loT == rightT = right
                | loT >  rightT = openCrop' right
                -- Spanning the split.
                | otherwise = Split (openCrop' left) t inc (openCrop' right)
                where
                (leftT, rightT) = toLeftRightTimeX t inc

-- ^ No Maybe! because in this system, it will just block if the value is unknown.
sampleB :: Behavior a -> Time -> a
sampleB b t = go b
    where
    tdi = toTime t
    go (Value a) = a
    go (Split left t' isLeft right)
        | tdi < t' || (tdi == t' && isLeft)
            = go left
        | otherwise
            = go right

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
    go !lo (Split left t isLeft right) !hi = do
        _ <- forkIO $ go lo left (if isLeft then X_Exactly t else X_JustBefore t)
        go (if isLeft then X_JustAfter t else X_Exactly t) right hi

-- | Event occurence
data Occ a = NoOcc | Occ a
    deriving (Eq,Show)

newtype Event a = Event { toOccB :: Behavior (Occ a) }

instance Show a => Show (Event a) where
    show e = "Event " ++ show (eventToList e)

listToE :: [(Time, a)] -> Event a
listToE [] = Event (Value NoOcc)
listToE ((t,a):es)
    = Event $ Split (Value NoOcc) t False
        (Split (Value (Occ a)) t True (toOccB (listToE es)))

eventToList :: Event a -> [(Time, a)]
eventToList (Event b) = go b
    where
    go (Value NoOcc) = []
    go (Value _) = error "eventToList: found non instantaneous Event occ."
    go (Split (Value (Occ a)) t True r) = (t,a) : go r
    go (Split l _ _ r) = go l ++ go r

step :: forall a . a -> Event a -> Behavior a
step initA (Event btop) = fromMaybe (Value initA) (go True btop)
    where
    -- Remove NoOcc. If NoOcc return Nothing
    go :: Bool -> Behavior (Occ a) -> Maybe (Behavior a)
    go False      (Value NoOcc) = Nothing
    go True       (Value NoOcc) = Just (Value initA)
    go _          (Value (Occ a)) = Just (Value a)
    go isLeftMost (Split left t inc right) = case (go isLeftMost left, go False right) of
        (Nothing, Nothing) -> Nothing
        (Just a , Nothing) -> Just a
        (Nothing, Just a ) -> Just a
        (Just a , Just b ) -> Just (Split a t inc b)

sourceEvent :: IO ( TimeX -> Time -> a -> TimeX -> IO ()
                  -- ^ Update the event
                  --      (knowlage start, knowlage start is , event time, event value, knowlage stop)
                  , Event a
                  )
sourceEvent = do
    -- TODO make this more efficient!
    updatesChan <- C.newChan
    let updater lo t a hi = C.writeChan updatesChan (lo, t, a, hi)
    updates <- C.getChanContents updatesChan
    let event = Event (go X_NegInf X_Inf updates)
        go _ _ [] = Value NoOcc -- This should never actually happen. We dont't close the chan.
        go minLo maxHi ((lo, t, a, hi):xs)
            | lo < minLo = error "Source Event: knowlage overlaps existing knowlage. DId you pass the wrong knowlage start time?"
            | hi > maxHi = error "Source Event: knowlage overlaps existing knowlage. DId you pass the wrong knowlage end time?"
            | tx < lo || tx > hi
                         = error "Source Event: event time is outside of knowlage span"
            | otherwise = (error "TODO") {-
                -- [minLow <= lo <= tx <= hi <= hiMax]

                -- Assuming
                -- [minLow < lo < tx < hi < hiMax]
                = Split
                    _
                    t False
                    ( Split
                        (Value a)
                        t True
                        ( case hi of
                            X_Exactly hiT   -> Split (Value NoOcc) hiT True (go rs)
                            X_JustAfter hiT -> Split (Value NoOcc) hiT True (go rs)
                        )
                    )
                    -}
            where
                (ls,rs) = partition (error "TODO") xs

                tx = X_Exactly t
        -- | otherwise = error "Source Event update: expected: knowlageStart <= eventT <= knowlageEnd"



    return ( updater
           , event
           )


instance Arbitrary a => Arbitrary (Behavior a) where
    arbitrary = do
        times <- orderedList
        go (nub times)
        where
        go :: [Time] -> Gen (Behavior a)
        go [] = Value <$> arbitrary
        go ts = do
            sizeL <- choose (0,length ts - 1)
            l <- go (take sizeL ts)
            let t = ts !! sizeL
            r <- go (drop (sizeL + 1) ts)
            oneof
                [ do -- single split
                    inc <- arbitrary
                    return (Split l t inc r)
                , do -- double split
                    a <- arbitrary
                    return (Split l t False (Split (Value a) t True r))
                ]


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
            let t = ts !! sizeL
            r <- go (drop (sizeL + 1) ts)
            a <- arbitrary
            return (Split l t False (Split (Value (Occ a)) t True r))
