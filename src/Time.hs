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
    , isExactlyDI
    , isJustAfterDI

    , ToTime (..)
    , ToTimeErr (..)
    , CompareTime (..)
    , DelayTime (..)
    , minTime

    , (>.)
    , (<.)
    , (==.)
    ) where

import Test.QuickCheck

-- EQSimple time
type Time = Integer -- TODO Int64? nanoseconds?

-- | Time with possible delay.
data TimeD
    = D_Exactly Time
    | D_JustAfter Time
    deriving (Show, Eq)

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
    = DI_Exactly Time
    | DI_JustAfter Time
    | DI_Inf
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
instance ToTime TimeD TimeDI where
    toTime (D_Exactly   t) = DI_Exactly   t
    toTime (D_JustAfter t) = DI_JustAfter t

class ToTimeErr a b where toTimeErr :: String -> a -> b
instance ToTimeErr TimeDI TimeD where
    toTimeErr err dit = case dit of
        DI_Exactly t -> D_Exactly t
        DI_JustAfter t -> D_JustAfter t
        DI_Inf -> error $ "toTimeErr: " ++ err

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

class DelayTime t where
    delayTime :: t -> t

instance DelayTime TimeD where
    delayTime (D_Exactly t)   = D_JustAfter t
    -- NOTE that we apply the general assumption that 2 infinitesimals == 1 infinitesmal
    delayTime (D_JustAfter t) = D_JustAfter t

instance DelayTime TimeDI where
    delayTime (DI_Exactly t)   = DI_JustAfter t
    -- NOTE that we apply the general assumption that 2 infinitesimals == 1 infinitesmal
    delayTime (DI_JustAfter t) = DI_JustAfter t
    delayTime DI_Inf           = DI_Inf

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
    fromInteger = DI_Exactly
    negate = error "TODO instance Num TimeDI negate"

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