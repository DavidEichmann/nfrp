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
    -- , Event
    -- , toOccB
    , sampleB
    -- , step
    , watchB
    ) where

import Control.Concurrent
-- import Data.Maybe (isNothing)
import Data.List (nub)
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
    deriving (Functor)

-- instance Semigroup (Behavior a) where

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

-- -- | Event occurence
-- data Occ a = Occ a | NoOcc

-- newtype Event a = Event { toOccB :: Behavior (Occ a) }

-- step :: a -> Event a -> Behavior a
-- step _ _ = _ -- use initial value with time at -Inf

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
