{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
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
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Time
    ( Time
    , TimeD (..)
    , TimeDI (..)
    , TimeX (..)
    , isExactlyDI
    , isJustAfterDI
    , secondsToTime

    , ToTime (..)
    , ToTimeErr (..)
    , CompareTime (..)
    , NeighborTimes (..)
    , Delayable (..)
    , ClosestTime (..)
    , minTime

    , (>.)
    , (<.)
    , (==.)
    ) where

import Data.Int
import Test.QuickCheck
import System.Random

-- Time id nanoseconds
type Time = Int64 -- TODO Int64?

secondsToTime :: Num a => a -> a
secondsToTime s = s * 1000000000

-- | Time with possible delay.
data TimeD
    = D_Exactly   {-# UNPACK #-} !Time
    | D_JustAfter {-# UNPACK #-} !Time
    deriving (Eq)

instance Show TimeD where
    show (D_Exactly t) = show t
    show (D_JustAfter t) = show t ++ "⁺"

instance Ord TimeD where
    compare (D_Exactly a) (D_Exactly b) = compare a b
    compare (D_JustAfter a) (D_JustAfter b) = compare a b
    compare (D_Exactly a) (D_JustAfter b) = case compare a b of
        LT -> LT
        EQ -> LT
        GT -> GT
    compare (D_JustAfter a) (D_Exactly b) = case compare a b of
        LT -> LT
        EQ -> GT
        GT -> GT

-- | Time with possible delay and possibly infinity.
data TimeDI
    = DI_Exactly   {-# UNPACK #-} !Time
    | DI_JustAfter {-# UNPACK #-} !Time
    | DI_Inf
    deriving (Show, Eq)

data TimeX
    = X_NegInf
    | X_JustBefore {-# UNPACK #-} !Time
    | X_Exactly    {-# UNPACK #-} !Time
    | X_JustAfter  {-# UNPACK #-} !Time
    | X_Inf
    deriving (Show, Eq)


type family BigTime a b where
    BigTime Time Time     = Time
    BigTime Time TimeD    = TimeD
    BigTime Time TimeDI   = TimeDI
    BigTime TimeD Time    = TimeD
    BigTime TimeD TimeD   = TimeD
    BigTime TimeD TimeDI  = TimeDI
    BigTime TimeDI Time   = TimeDI
    BigTime TimeDI TimeD  = TimeDI
    BigTime TimeDI TimeDI = TimeDI

class ToTime a b where toTime :: a -> b
instance ToTime Time   Time    where toTime = id
instance ToTime TimeD  TimeD   where toTime = id
instance ToTime TimeDI TimeDI  where toTime = id
instance ToTime Time   TimeD   where
    toTime = D_Exactly
instance ToTime Time TimeDI where
    toTime = DI_Exactly
instance ToTime Time TimeX where
    toTime = X_Exactly
instance ToTime TimeD TimeDI where
    toTime (D_Exactly   t) = DI_Exactly   t
    toTime (D_JustAfter t) = DI_JustAfter t
instance ToTime TimeD TimeX where
    toTime (D_Exactly   t) = X_Exactly   t
    toTime (D_JustAfter t) = X_JustAfter t
instance ToTime TimeDI TimeX where
    toTime (DI_Exactly   t) = X_Exactly   t
    toTime (DI_JustAfter t) = X_JustAfter t
    toTime DI_Inf = X_Inf

class ToTimeErr a b where toTimeErr :: String -> a -> b
instance ToTimeErr TimeDI TimeD where
    toTimeErr err dit = case dit of
        DI_Exactly t -> D_Exactly t
        DI_JustAfter t -> D_JustAfter t
        DI_Inf -> error $ "toTimeErr (TimeDI -> TimeD): " ++ err
instance ToTimeErr TimeX TimeDI where
    toTimeErr err dit = case dit of
        X_Exactly t -> DI_Exactly t
        X_JustAfter t -> DI_JustAfter t
        X_Inf -> DI_Inf
        _ -> error $ "toTimeErr (TimeX TimeDI): " ++ err

class NeighborTimes a where
    -- True if no time inbetween can possibly be represented.
    neighbotTimes :: a -> a -> Bool
instance NeighborTimes TimeX where
    neighbotTimes X_Inf X_Inf = True
    neighbotTimes X_NegInf X_NegInf = True
    neighbotTimes (X_JustBefore t) (X_JustBefore t') = t == t'
    neighbotTimes (X_JustBefore t) (X_Exactly t') = t == t'
    neighbotTimes (X_Exactly t) (X_JustBefore t') = t == t'
    neighbotTimes (X_Exactly t) (X_Exactly t') = t == t'
    neighbotTimes (X_Exactly t) (X_JustAfter t') = t == t'
    neighbotTimes (X_JustAfter t) (X_JustBefore t') = t == t'
    neighbotTimes (X_JustAfter t) (X_Exactly t') = t == t'
    neighbotTimes _ _ = False

isExactlyDI :: TimeDI -> Bool
isExactlyDI (DI_Exactly _) = True
isExactlyDI _ = False

isJustAfterDI :: TimeDI -> Bool
isJustAfterDI (DI_JustAfter _) = True
isJustAfterDI _ = False

(<.) :: CompareTime a b => a -> b -> Bool
a <. b = LT == compareTime a b

(>.) :: CompareTime a b => a -> b -> Bool
a >. b = GT == compareTime a b

(==.) :: CompareTime a b => a -> b -> Bool
a ==. b = EQ == compareTime a b

minTime :: (c ~ BigTime a b, ToTime a c, ToTime b c, Ord c) => a -> b -> c
minTime a b = min (toTime a) (toTime b)

class CompareTime a b where
    compareTime :: a -> b -> Ordering
    default compareTime :: CompareTime b a => a -> b -> Ordering
    compareTime = flip compareTime

instance CompareTime Time   Time   where compareTime = compare
instance CompareTime TimeD  TimeD  where compareTime = compare
instance CompareTime TimeDI TimeDI where compareTime = compare

instance CompareTime Time   TimeD where compareTime = flip compareTimeFromConvert
instance CompareTime TimeD  Time  where compareTime = compareTimeFromConvert

compareTimeFromConvert :: (Ord a, ToTime b a) => a -> b -> Ordering
compareTimeFromConvert a b = compare a (toTime b)

instance Ord TimeDI where
    compare DI_Inf DI_Inf = EQ
    compare DI_Inf _ = GT
    compare _ DI_Inf = LT
    compare (DI_Exactly   a) (DI_Exactly   b) = compare a b
    compare (DI_JustAfter a) (DI_JustAfter b) = compare a b
    compare (DI_Exactly   a) (DI_JustAfter b) = case compare a b of
        LT -> LT
        EQ -> LT
        GT -> GT
    compare (DI_JustAfter a) (DI_Exactly   b) = case compare a b of
        LT -> LT
        EQ -> GT
        GT -> GT

instance Ord TimeX where
    compare X_NegInf X_NegInf = EQ
    compare X_NegInf _        = LT
    compare _        X_NegInf = GT

    compare X_Inf X_Inf = EQ
    compare X_Inf _     = GT
    compare _     X_Inf = LT

    compare (X_JustBefore a) (X_JustBefore b) = compare a b
    compare (X_Exactly    a) (X_Exactly    b) = compare a b
    compare (X_JustAfter  a) (X_JustAfter  b) = compare a b

    compare (X_JustBefore a) (X_Exactly    b) = compareBiased LT a b
    compare (X_JustBefore a) (X_JustAfter  b) = compareBiased LT a b
    compare (X_Exactly    a) (X_JustAfter  b) = compareBiased LT a b

    compare (X_Exactly    a) (X_JustBefore b) = compareBiased GT a b
    compare (X_JustAfter  a) (X_JustBefore b) = compareBiased GT a b
    compare (X_JustAfter  a) (X_Exactly    b) = compareBiased GT a b

compareBiased :: Ord a => Ordering -> a -> a -> Ordering
compareBiased o a b = case compare a b of
    LT -> LT
    EQ -> o
    GT -> GT


class Delayable t where
    delay :: t -> t

instance Delayable TimeD where
    delay (D_Exactly t)   = D_JustAfter t
    -- NOTE that we apply the general assumption that 2 infinitesimals == 1 infinitesmal
    delay (D_JustAfter t) = D_JustAfter t

instance Delayable TimeDI where
    delay (DI_Exactly t)   = DI_JustAfter t
    -- NOTE that we apply the general assumption that 2 infinitesimals == 1 infinitesmal
    delay (DI_JustAfter t) = DI_JustAfter t
    delay DI_Inf           = DI_Inf

instance Delayable TimeX where
    delay (X_JustBefore t) = X_JustAfter t
    delay (X_Exactly t)   = X_JustAfter t
    -- NOTE that we apply the general assumption that 2 infinitesimals == 1 infinitesmal
    delay (X_JustAfter t) = X_JustAfter t
    delay t           = t

instance Num TimeD where
    (D_Exactly a) + (D_Exactly b) = D_Exactly (a+b)
    (D_Exactly a) + (D_JustAfter b) = D_JustAfter (a+b)
    (D_JustAfter a) + (D_Exactly b) = D_JustAfter (a+b)
    (D_JustAfter a) + (D_JustAfter b) = D_JustAfter (a+b)

    (D_Exactly a) - (D_Exactly b) = D_Exactly (a-b)
    (D_Exactly _) - (D_JustAfter _) = error "Num TimeD: Can't subtract D_Exactly - D_JustAfter"
    (D_JustAfter a) - (D_Exactly b) = D_JustAfter (a-b)
    (D_JustAfter a) - (D_JustAfter b) = D_JustAfter (a-b)

    0 * _ = 0
    _ * 0 = 0
    (D_Exactly a) * (D_Exactly b) = D_Exactly (a*b)
    ad@(D_Exactly a) * bd@(D_JustAfter b)
        | a > 0 = D_JustAfter (a*b)
        | otherwise = error $ "Num TimeD: Can't multiply " ++ show ad ++ " * " ++ show bd
    ad@(D_JustAfter a) * bd@(D_Exactly b)
        | b > 0 = D_JustAfter (a*b)
        | otherwise = error $ "Num TimeD: Can't multiply " ++ show ad ++ " * " ++ show bd
    ad@(D_JustAfter a) * bd@(D_JustAfter b)
        | signum a == signum b = D_JustAfter (a*b)
        | otherwise = error $ "Num TimeD: Can't multiply " ++ show ad ++ " * " ++ show bd

    abs (D_Exactly a) = (D_Exactly (abs a))
    abs (D_JustAfter a) = (D_JustAfter (abs a))
    signum (D_Exactly a) = D_Exactly (signum a)
    signum (D_JustAfter a) = D_Exactly (signum a)
    fromInteger = D_Exactly . fromInteger

    negate (D_Exactly a) = (D_Exactly (negate a))
    negate justAfter = error $ "Num TimeD: Can't negate " ++ show justAfter

instance Num TimeDI where
    (DI_Exactly a) + (DI_Exactly b) = DI_Exactly (a+b)
    (DI_Exactly a) + (DI_JustAfter b) = DI_JustAfter (a+b)
    (DI_JustAfter a) + (DI_Exactly b) = DI_JustAfter (a+b)
    (DI_JustAfter a) + (DI_JustAfter b) = DI_JustAfter (a+b)
    DI_Inf + _ = DI_Inf
    _ + DI_Inf = DI_Inf
    (*) = error "TODO instance Num TimeDI (*)"
    abs (DI_Exactly a) = (DI_Exactly (abs a))
    abs (DI_JustAfter a) = (DI_JustAfter (abs a))
    abs DI_Inf = DI_Inf
    signum = error "TODO instance Num TimeDI signum"
    fromInteger = DI_Exactly . fromInteger
    negate = error "TODO instance Num TimeDI negate"

instance Num TimeX where
    (X_Exactly a) + (X_Exactly b) = X_Exactly (a+b)
    (X_JustAfter a) + (X_JustAfter b) = X_JustAfter (a+b)
    (X_JustBefore a) + (X_JustBefore b) = X_JustBefore (a+b)
    (X_Exactly a) + (X_JustAfter b) = X_JustAfter (a+b)
    (X_Exactly a) + (X_JustBefore b) = X_JustBefore (a+b)
    (X_JustAfter a) + (X_Exactly b) = X_JustAfter (a+b)
    (X_JustBefore b) + (X_Exactly a) = X_JustBefore (a+b)
    (X_JustBefore _) + (X_JustAfter _) = error "(X_JustBefore _) + (X_JustAfter _)"
    (X_JustAfter _) + (X_JustBefore _) = error "(X_JustBefore _) + (X_JustAfter _)"
    X_Inf + X_NegInf = error "X_Inf + XNegIng"
    X_NegInf + X_Inf = error "X_Inf + XNegIng"
    X_Inf + _ = X_Inf
    _ + X_Inf = X_Inf
    X_NegInf + _ = X_NegInf
    _ + X_NegInf = X_NegInf

    (*) = error "TODO instance Num TimeX (*)"

    abs X_NegInf = X_Inf
    abs t@(X_JustBefore a)
        | a < 0     = (X_JustAfter (abs a))
        | otherwise = t
    abs (X_Exactly a) = (X_Exactly (abs a))
    abs t@(X_JustAfter a)
        | a < 0     = (X_JustBefore (abs a))
        | otherwise = t
    abs X_Inf = X_Inf

    signum X_NegInf = -1
    signum (X_JustBefore a) = X_Exactly (signum a)
    signum (X_Exactly a)    = X_Exactly (signum a)
    signum (X_JustAfter a)  = X_Exactly (signum a)
    signum X_Inf = 1

    fromInteger = X_Exactly . fromInteger

    negate X_NegInf = X_Inf
    negate (X_JustBefore a) = X_JustAfter (-a)
    negate (X_Exactly a)    = X_Exactly (-a)
    negate (X_JustAfter a)  = X_JustBefore (-a)
    negate X_Inf = X_NegInf

class ClosestTime a where closestTime :: a -> Time
instance ClosestTime TimeD where
    closestTime (D_Exactly   t) = t
    closestTime (D_JustAfter t) = t

instance Arbitrary TimeD where
    arbitrary = oneof
                    [ D_Exactly   <$> arbitrary
                    , D_JustAfter <$> arbitrary
                    ]
instance Arbitrary TimeDI where
    arbitrary = frequency
                    [ (10, DI_Exactly   <$> arbitrary)
                    , (10, DI_JustAfter <$> arbitrary)
                    , (1, pure DI_Inf)
                    ]
instance Arbitrary TimeX where
    arbitrary = frequency
                    [ (10, X_Exactly   <$> arbitrary)
                    , (10, X_JustAfter <$> arbitrary)
                    , (10, X_JustBefore <$> arbitrary)
                    , (1, pure X_Inf)
                    , (1, pure X_NegInf)
                    ]

instance Random TimeD where
    random g = let
        (del, g') = random g
        (t, g'') = random g'
        in (if del then D_JustAfter t else D_Exactly t, g'')
    randomR (loD, hiD) g = let
        lo :: Time
        lo = case loD of
                D_Exactly t' -> t'
                D_JustAfter t' -> t'
        hi :: Time
        hi = case hiD of
                D_Exactly t' -> t'
                D_JustAfter t' -> t'
        (del, g') = random g
        (t, g'') = randomR (lo, hi) g'
        tdIsh = if del then D_JustAfter t else D_Exactly t
        in (max loD (min tdIsh hiD), g'')