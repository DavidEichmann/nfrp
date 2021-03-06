{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
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

module TimeSpan where

import Data.List (foldl', group, sort)
import Data.Maybe (catMaybes, isJust, maybeToList)
import Data.Binary (Binary)
import Data.String (IsString(..))
import Data.Text.Prettyprint.Doc (Pretty(..))
import GHC.Generics (Generic)
import Test.QuickCheck hiding (once)

import Time

data AllOr a
    = All   -- ^ All of time [-Inf, Inf]
    | Or !a  -- ^ Just that a.
    deriving stock (Show, Generic) -- NOT Ord
    deriving anyclass (Binary)

data AllOrIncExc a
    = AIX_All   -- ^ all
    | AIX_Inc a -- ^ inclusive
    | AIX_Exc a -- ^ exclusive

-- Half spaces
newtype LeftSpaceExc  = LeftSpaceExc  Time   -- ^ [[ LeftSpaceExc  t' ]] = { t | t < t' }
    deriving stock (Eq, Ord, Generic)
    deriving anyclass (Binary)
newtype RightSpaceExc = RightSpaceExc Time   -- ^ [[ RightSpaceExc t' ]] = { t | t > t' }
    deriving stock (Eq, Ord, Generic)
    deriving anyclass (Binary)

instance Show LeftSpaceExc where
    show (LeftSpaceExc t) = "←" ++ show t ++ "○"
instance Show RightSpaceExc where
    show (RightSpaceExc t) = "○" ++ show t ++ "→"

deriving instance Eq (AllOr LeftSpaceExc)
deriving instance Eq (AllOr RightSpaceExc)


-- Half spaces
newtype LeftSpaceInc  = LeftSpaceInc  Time   -- ^ [[ LeftSpaceInc  t' ]] = { t | t <= t' }
    deriving stock (Eq, Ord, Generic)
    deriving anyclass (Binary)
newtype RightSpaceInc = RightSpaceInc Time   -- ^ [[ RightSpaceInc t' ]] = { t | t >= t' }
    deriving stock (Eq, Ord, Generic)
    deriving anyclass (Binary)

instance Show LeftSpaceInc where
    show (LeftSpaceInc t) = "←" ++ show t ++ "●"
instance Show RightSpaceInc where
    show (RightSpaceInc t) = "●" ++ show t ++ "→"

deriving instance Eq (AllOr LeftSpaceInc)
deriving instance Eq (AllOr RightSpaceInc)

-- [[ SpanIncExc l r ]] = l `intersect` r
-- Non empty
data SpanExc
    = SpanExc
        !(AllOr RightSpaceExc) -- ^ Time span left  bound Exclusive. All == Inclusive -Inf
        !(AllOr LeftSpaceExc)  -- ^ Time span right bound Exclusive. All == !Inclusive! Inf
    deriving stock (Eq, Generic) -- NOT Ord
    deriving anyclass (Binary)
data SpanInc
    = SpanInc
        !(AllOr RightSpaceInc) -- ^ Time span left  bound Inclusive. All == Inclusive -Inf
        !(AllOr LeftSpaceInc)  -- ^ Time span right bound Inclusive. All == !Inclusive! Inf
    deriving stock (Eq, Generic) -- NOT Ord
    deriving anyclass (Binary)

instance Show SpanExc where
    show s = "SpanExc " ++ spanExcShowCompact s

instance Pretty SpanExc where
    pretty = fromString . spanExcShowCompact

spanExcShowCompact :: SpanExc -> String
spanExcShowCompact (SpanExc allOrR allOrL) = "[" ++ rt  ++ " " ++ lt ++ "]"
    where
    rt = case allOrR of
        All -> "←"
        Or r -> show r
    lt = case allOrL of
        All -> "→"
        Or l -> show l

-- Inclusive start Exclusive end span.
spanExc :: Maybe Time -> Maybe Time -> SpanExc
spanExc lo hi
    = case spanExcMaybe lo hi of
        Nothing -> error "spanExc: lo >= hi"
        Just x -> x

-- Inclusive start Exclusive end span.
-- Nothing if the input times are not strictly increasing.
spanExcMaybe :: Maybe Time -> Maybe Time -> Maybe SpanExc
spanExcMaybe lo hi = (maybe All (Or . RightSpaceExc) lo) `intersect`
                        (maybe All (Or . LeftSpaceExc) hi)

spanExcMinT :: SpanExc -> TimeX
spanExcMinT (SpanExc All _) = X_NegInf
spanExcMinT (SpanExc (Or (RightSpaceExc t)) _) = X_JustAfter t

spanExcMaxT :: SpanExc -> TimeX
spanExcMaxT (SpanExc _ All) = X_Inf
spanExcMaxT (SpanExc _ (Or (LeftSpaceExc t))) = X_JustBefore t

spanExcJustBefore :: SpanExc -> Maybe Time
spanExcJustBefore (SpanExc All _) = Nothing
spanExcJustBefore (SpanExc (Or (RightSpaceExc t)) _) = Just t

spanExcJustAfter :: SpanExc -> Maybe Time
spanExcJustAfter (SpanExc _ All) = Nothing
spanExcJustAfter (SpanExc _ (Or (LeftSpaceExc t))) = Just t

spanExcSameLowerBound :: SpanExc -> SpanExc -> Bool
spanExcSameLowerBound a b = spanExcJustBefore a == spanExcJustBefore b

data Span = Span
    { spanLo :: SpanBound
    , spanHi :: SpanBound
    }
data SpanBound
    = Open
    | ClosedInc Time
    | ClosedExc Time
    deriving (Eq, Ord)

mkSpan :: SpanBound -> SpanBound -> Maybe Span
mkSpan l h = case (l, h) of
    (Open,  _  ) -> Just (Span Open h)
    (_   , Open) -> Just (Span l Open)
    (ClosedInc a, ClosedInc b)
        | a <= b      -> Just (Span l Open)
        | otherwise   -> Nothing
    (ClosedExc a, ClosedExc b)
        | a < b       -> Just (Span l Open)
        | otherwise   -> Nothing
    (ClosedExc a, ClosedInc b)
        | a < b       -> Just (Span l Open)
        | otherwise   -> Nothing
    (ClosedInc a, ClosedExc b)
        | a < b       -> Just (Span l Open)
        | otherwise   -> Nothing

class Intersect a b c | a b -> c where
    intersect :: a -> b -> c

-- a `difference` b == a `intersect` (invert b)
class Difference a b c | a b -> c where
    difference :: a -> b -> c

class NeverAll a
instance NeverAll LeftSpaceExc
instance NeverAll RightSpaceExc
instance NeverAll LeftSpaceInc
instance NeverAll RightSpaceInc

class Contains a b where
    contains :: a -> b -> Bool

-- | Covering all of time
class AllT a where allT :: a
instance AllT SpanExc where allT = SpanExc All All
instance AllT Span where allT = Span Open Open

timeToSpan :: Time -> Span
timeToSpan t = Span (ClosedInc t) (ClosedInc t)

timeSpanToSpan :: TimeSpan -> Span
timeSpanToSpan (DS_Point t) = timeToSpan t
timeSpanToSpan (DS_SpanExc tspan) = spanExcToSpan tspan

spanExcToSpan :: SpanExc -> Span
spanExcToSpan (SpanExc l r)
    = Span
        (case l of
            All -> Open
            Or (RightSpaceExc t) -> ClosedExc t
        )
        (case r of
            All -> Open
            Or (LeftSpaceExc t) -> ClosedExc t
        )

beforeSpan :: Span -> Maybe Span
beforeSpan (Span l _) = case l of
    Open -> Nothing
    ClosedInc t -> Just (Span Open (ClosedExc t))
    ClosedExc t -> Just (Span Open (ClosedInc t))

afterSpan :: Span -> Maybe Span
afterSpan (Span _ r) = case r of
    Open -> Nothing
    ClosedInc t -> Just (Span (ClosedExc t) Open)
    ClosedExc t -> Just (Span (ClosedInc t) Open)

class IsAllT a where isAllT :: a -> Bool
instance IsAllT LeftSpaceExc where isAllT _ = False
instance IsAllT RightSpaceExc where isAllT _ = False
instance IsAllT LeftSpaceInc where isAllT _ = False
instance IsAllT RightSpaceInc where isAllT _ = False

instance Intersect Span Span (Maybe Span) where
    intersect (Span l1 h1) (Span l2 h2) = mkSpan l h
        where
        l = case (l1, l2) of
                (Open, _) -> l2
                (_, Open) -> l1
                (ClosedInc a, ClosedInc b) -> ClosedInc (max a b)
                (ClosedExc a, ClosedExc b) -> ClosedExc (max a b)
                (ClosedInc a, ClosedExc b) -> case compare a b of
                    LT -> ClosedExc b
                    EQ -> ClosedExc b
                    GT -> ClosedInc a
                (ClosedExc a, ClosedInc b) -> case compare a b of
                    LT -> ClosedInc b
                    EQ -> ClosedExc b
                    GT -> ClosedExc a
        h = case (h1, h2) of
                (Open, _) -> h2
                (_, Open) -> h1
                (ClosedInc a, ClosedInc b) -> ClosedInc (min a b)
                (ClosedExc a, ClosedExc b) -> ClosedExc (min a b)
                (ClosedInc a, ClosedExc b) -> case compare a b of
                    LT -> ClosedInc a
                    EQ -> ClosedExc a
                    GT -> ClosedExc b
                (ClosedExc a, ClosedInc b) -> case compare a b of
                    LT -> ClosedExc a
                    EQ -> ClosedExc a
                    GT -> ClosedInc b

instance Intersect LeftSpaceExc RightSpaceExc (Maybe SpanExc) where intersect = flip intersect
instance Intersect RightSpaceExc LeftSpaceExc (Maybe SpanExc) where
    intersect r@(RightSpaceExc lo) l@(LeftSpaceExc hi)
        | lo < hi = Just (SpanExc (Or r) (Or l))
        | otherwise = Nothing
instance Intersect Time Time (Maybe Time) where intersect a b = if a == b then Just a else Nothing
instance Intersect Time SpanExc (Maybe Time) where intersect = flip intersect
instance Intersect SpanExc Time (Maybe Time) where
    intersect tspan t = if tspan `contains` t then Just t else Nothing
instance Intersect SpanExc LeftSpaceExc (Maybe SpanExc) where intersect = flip intersect
instance Intersect LeftSpaceExc SpanExc (Maybe SpanExc) where
    intersect ls (SpanExc r l) = r `intersect` (l `intersect` ls)
instance Intersect SpanExc RightSpaceExc (Maybe SpanExc) where intersect = flip intersect
instance Intersect RightSpaceExc SpanExc (Maybe SpanExc) where
    intersect rs (SpanExc r l) = l `intersect` (r `intersect` rs)
instance Intersect SpanExc SpanExc (Maybe SpanExc) where
    intersect s (SpanExc r l) = intersect l =<< (r `intersect` s)
instance Intersect (AllOr LeftSpaceExc ) LeftSpaceExc  LeftSpaceExc    where intersect = allOrIntersect
instance Intersect (AllOr RightSpaceExc) RightSpaceExc RightSpaceExc   where intersect = allOrIntersect
instance Intersect (AllOr RightSpaceExc) SpanExc       (Maybe SpanExc) where intersect = allOrIntersectMaybe
instance Intersect (AllOr LeftSpaceExc ) SpanExc       (Maybe SpanExc) where intersect = allOrIntersectMaybe
instance Intersect RightSpaceExc RightSpaceExc RightSpaceExc where
    intersect (RightSpaceExc a) (RightSpaceExc b) = RightSpaceExc (max a b)
instance Intersect (AllOr LeftSpaceExc ) (AllOr RightSpaceExc) (Maybe SpanExc) where intersect = flip intersect
instance Intersect (AllOr RightSpaceExc) (AllOr LeftSpaceExc)  (Maybe SpanExc) where
    intersect (Or rs) (Or ls) = rs `intersect` ls
    intersect allOrRs allOrLs = Just (SpanExc allOrRs allOrLs)
instance Intersect (AllOr LeftSpaceExc) RightSpaceExc (Maybe SpanExc) where intersect = flip intersect
instance Intersect RightSpaceExc (AllOr LeftSpaceExc) (Maybe SpanExc) where
    intersect rs (Or ls) = rs `intersect` ls
    intersect rs All = Just (SpanExc (Or rs) All)
instance Intersect LeftSpaceExc (AllOr RightSpaceExc) (Maybe SpanExc) where intersect = flip intersect
instance Intersect (AllOr RightSpaceExc) LeftSpaceExc (Maybe SpanExc) where
    intersect (Or rs) ls = rs `intersect` ls
    intersect All ls = Just (SpanExc All (Or ls))
instance Intersect (Either Time SpanExc) (Either Time SpanExc) (Maybe (Either Time SpanExc)) where
    intersect (Left a)  (Left b)  = Left  <$> intersect a b
    intersect (Right a) (Left b)  = Left  <$> intersect a b
    intersect (Left b)  (Right a) = Left  <$> intersect a b
    intersect (Right b) (Right a) = Right <$> intersect a b
instance Intersect (Either Time SpanExc) Time (Maybe Time) where
    intersect (Left a)  b = a `intersect` b
    intersect (Right a) b = a `intersect` b

instance Difference LeftSpaceExc LeftSpaceExc (Maybe (Time, SpanExc)) where
    difference (LeftSpaceExc a) (LeftSpaceExc b) = (b,) <$> spanExcMaybe (Just b) (Just a)
instance Difference RightSpaceExc RightSpaceExc (Maybe (SpanExc, Time)) where
    difference (RightSpaceExc a) (RightSpaceExc b) = (,b) <$> spanExcMaybe (Just a) (Just b)
instance Difference SpanExc SpanExc (Maybe (SpanExc, Time), Maybe (Time, SpanExc)) where
    difference a (SpanExc rs ls) = (a `difference` rs, a `difference` ls)
instance Difference SpanExc LeftSpaceExc (Maybe (Time, SpanExc)) where
    difference s (LeftSpaceExc b) = (b,) <$> s `intersect` (RightSpaceExc b)
instance Difference SpanExc RightSpaceExc (Maybe (SpanExc, Time)) where
    difference s (RightSpaceExc b) = (,b) <$> s `intersect` (LeftSpaceExc b)
instance Difference SpanExc Time [SpanExc] where
    difference tspan t = catMaybes [tspan `intersect` LeftSpaceExc t, tspan `intersect` RightSpaceExc t]
instance Difference Time SpanExc (Maybe Time) where
    difference t tspan = if tspan `contains` t
        then Just t
        else Nothing
instance Difference (Either Time SpanExc) (Either Time SpanExc) [Either Time SpanExc] where
    difference (Left a) (Left b)
        | a == b = []
        | otherwise = [Left a]
    difference (Left a) (Right b) = fmap Left . maybeToList $ a `difference` b
    difference (Right a) (Left b) = Right <$> a `difference` b
    difference (Right a) (Right b) = concat
        [ l ++ r
        | let (x, y) = a `difference` b
        , let l = case x of
                        Nothing -> []
                        Just (tspan, t) -> [Right tspan, Left t]
        , let r = case y of
                        Nothing -> []
                        Just (t, tspan) -> [Right tspan, Left t]
        ]
instance Difference [Either Time SpanExc] (Either Time SpanExc) [Either Time SpanExc] where
    difference a b = concatMap (`difference` b) a
instance Difference (Either Time SpanExc) [Either Time SpanExc] [Either Time SpanExc] where
    difference a bs = foldl' difference [a] bs



instance Contains Time Time where
    contains = (==)
instance Contains LeftSpaceExc TimeX where
    contains (LeftSpaceExc a) t = t < toTime a
instance Contains RightSpaceExc TimeX where
    contains (RightSpaceExc a) t = t > toTime a
instance Contains LeftSpaceInc Time where
    contains (LeftSpaceInc ls) t = t <= ls
instance Contains LeftSpaceExc Time where
    contains (LeftSpaceExc ls) t = t < ls
instance Contains RightSpaceExc Time where
    contains (RightSpaceExc rs) t = t > rs
instance Contains SpanExc Time where
    contains (SpanExc rs ls) t = ls `contains` t && rs `contains` t
instance Contains SpanExc TimeX where
    contains (SpanExc rs ls) t = ls `contains` t && rs `contains` t
instance Contains (Either Time SpanExc) Time where
    contains (Left t') t = t' `contains` t
    contains (Right tspan) t = tspan `contains` t
instance Contains LeftSpaceExc LeftSpaceExc where
    contains (LeftSpaceExc a) (LeftSpaceExc b) = a >= b
instance Contains RightSpaceExc RightSpaceExc where
    contains (RightSpaceExc a) (RightSpaceExc b) = a <= b
instance Contains LeftSpaceExc SpanExc where
    contains ls (SpanExc _ allOrLs) = ls `contains` allOrLs
instance Contains RightSpaceExc SpanExc where
    contains rs (SpanExc allOrRs _) = rs `contains` allOrRs
instance Contains SpanExc SpanExc where
    contains (SpanExc r l) s = r `contains` s && l `contains` s
-- instance (Contains a b, IsAllT a) => Contains a (AllOr b) where
--     contains a All    = isAllT a
--     contains a (Or b) = a `contains` b
-- instance (Contains a b, IsAllT a) => Contains (AllOr a) b where
--     contains All _ = True
--     contains (Or a) b = a `contains` b

-- intersects :: Intersect a b (Maybe c) => a -> b -> Bool
-- intersects a b = isJust (a `intersect` b)

data SplitSpanExc
    = FullyLeftOfT SpanExc
    | FullyRightOfT SpanExc
    | SplitByT SpanExc SpanExc

splitSpanExcAt :: SpanExc -> Time -> SplitSpanExc
splitSpanExcAt tspan t = case (tspan `intersect` LeftSpaceExc t, tspan `intersect` RightSpaceExc t) of
    (Nothing, Nothing) -> error "splitSpanExcAt: Impossible!"
    (Just l, Nothing) -> FullyLeftOfT l
    (Nothing, Just r) -> FullyRightOfT r
    (Just l, Just r) -> SplitByT l r

splitSpanExcAtErr :: SpanExc -> Time -> (SpanExc, SpanExc)
splitSpanExcAtErr s t = case splitSpanExcAt s t of
    SplitByT l r -> (l, r)
    _ -> error "splitSpanExcAtErr"


{-
-- | If the left arg ends exactly on the start of the right arg, return the
-- joined span and the time at which they are joined (such that splitting on
-- that time will give the original spans).
endsOn :: SpanExc -> SpanExc -> Maybe (SpanExc, TimeD)
endsOn (SpanExc allOrRs (Or (LeftSpaceExc hi))) (SpanExc (Or (RightSpaceExc lo)) allOrLs)
    | hi == lo  = Just (SpanExc allOrRs allOrLs, lo)
endsOn _ _ = Nothing

instantaneous :: SpanExc -> Maybe Time
instantaneous (SpanExc (Or (RightSpaceExc (D_Exactly t))) (Or (LeftSpaceExc (D_JustAfter t'))))
    | t == t' = Just t
instantaneous _ = Nothing

splitSpanAtErr :: SpanExc -> TimeD -> String -> (SpanExc, SpanExc)
splitSpanAtErr tspan t err = case splitSpanAt tspan t of
    (Just lspan, Just rspan) -> (lspan, rspan)
    _ -> error $ err ++ ": splitSpanAtErr: Found a (Split _ (" ++ show t ++ ") _) but are in span: " ++ show tspan

-}
spanExcBoundaries :: SpanExc -> (TimeX, TimeX)
spanExcBoundaries (SpanExc r l) = (lo, hi)
    where
    lo = case r of
            All -> X_NegInf
            (Or (RightSpaceExc loT)) -> X_Exactly loT
    hi = case l of
            All -> X_Inf
            (Or (LeftSpaceExc hiT)) -> X_Exactly hiT



data SpanIncX = SpanIncX TimeX TimeX -- Lo hi inclusive.

--
-- Time SpanIncExc stuff
--

-- [[ SpanIncExc l r ]] = l `intersect` r
data SpanIncExc
    = SpanIncExc
        (AllOr RightSpaceInc) -- ^ Time span left  bound Inclusive. All == Inclusive -Inf
        (AllOr LeftSpaceExc)  -- ^ Time span right bound Exclusive. All == !Inclusive! Inf
    deriving (Eq) -- NOT Ord

instance Show SpanIncExc where
    show (SpanIncExc allOrR allOrL) = "SpanIncExc [" ++ rt  ++ " " ++ lt ++ "]"
        where
        rt = case allOrR of
            All -> "←"
            Or r -> show r
        lt = case allOrL of
            All -> "→"
            Or l -> show l

-- Inclusive start Exclusive end span.
spanIncExc :: Maybe Time -> Maybe Time -> SpanIncExc
spanIncExc lo hi
    = case spanIncExcMaybe lo hi of
        Nothing -> error "spanIncExc: lo >= hi"
        Just x -> x

-- Inclusive start Exclusive end span.
-- Nothing if the input times are not strictly increasing.
spanIncExcMaybe :: Maybe Time -> Maybe Time -> Maybe SpanIncExc
spanIncExcMaybe lo hi = (maybe All (Or . RightSpaceInc) lo) `intersect`
                        (maybe All (Or . LeftSpaceExc) hi)

data SpanExcInc
    = SpanExcInc
        (AllOr RightSpaceExc) -- ^ Time span left  bound Exclusive. All == Inclusive -Inf
        (AllOr LeftSpaceInc)  -- ^ Time span right bound Inclusive. All == !Inclusive! Inf
    deriving (Eq) -- NOT Ord

instance Show SpanExcInc where
    show (SpanExcInc allOrR allOrL) = "SpanExcInc [" ++ rt  ++ " " ++ lt ++ "]"
        where
        rt = case allOrR of
            All -> "←"
            Or r -> show r
        lt = case allOrL of
            All -> "→"
            Or l -> show l

spanExcInc :: Maybe Time -> Maybe Time -> SpanExcInc
spanExcInc lo hi
    = case spanExcIncMaybe lo hi of
        Nothing -> error "spanExcInc: lo >= hi"
        Just x -> x

spanExcIncMaybe :: Maybe Time -> Maybe Time -> Maybe SpanExcInc
spanExcIncMaybe lo hi = (maybe All (Or . RightSpaceExc) lo) `intersect`
                        (maybe All (Or . LeftSpaceInc) hi)

-- -- More convenient span creating functions
-- spanToInc :: Time -> SpanIncExc
-- spanToInc hi= spanIncExc Nothing (Just $ delay $ toTime hi)
-- spanToExc :: Time -> SpanIncExc
-- spanToExc hi= spanIncExc Nothing (Just $ toTime hi)
-- spanFromInc :: Time -> SpanIncExc
-- spanFromInc lo = spanIncExc (Just $ toTime lo) Nothing
-- spanFromExc :: Time -> SpanIncExc
-- spanFromExc lo = spanIncExc (Just $ delay $ toTime lo) Nothing
-- spanFromIncToExc :: Time -> Time -> SpanIncExc
-- spanFromIncToExc lo hi = spanIncExc (Just $ toTime lo) (Just $ toTime hi)
-- spanFromIncToInc :: Time -> Time -> SpanIncExc
-- spanFromIncToInc lo hi = spanIncExc (Just $ toTime lo) (Just $ delay $ toTime hi)
-- spanFromExcToExc :: Time -> Time -> SpanIncExc
-- spanFromExcToExc lo hi = spanIncExc (Just $ delay $ toTime lo) (Just $ toTime hi)
-- spanFromExcToInc :: Time -> Time -> SpanIncExc
-- spanFromExcToInc lo hi = spanIncExc (Just $ delay $ toTime lo) (Just $ delay $ toTime hi)

instance Intersect LeftSpaceExc RightSpaceInc (Maybe SpanIncExc) where intersect = flip intersect
instance Intersect RightSpaceInc LeftSpaceExc (Maybe SpanIncExc) where
    intersect r@(RightSpaceInc lo) l@(LeftSpaceExc hi)
        | lo < hi = Just (SpanIncExc (Or r) (Or l))
        | otherwise = Nothing
instance Intersect LeftSpaceInc RightSpaceExc (Maybe SpanExcInc) where intersect = flip intersect
instance Intersect RightSpaceExc LeftSpaceInc (Maybe SpanExcInc) where
    intersect r@(RightSpaceExc lo) l@(LeftSpaceInc hi)
        | lo < hi = Just (SpanExcInc (Or r) (Or l))
        | otherwise = Nothing
instance Intersect SpanIncExc LeftSpaceExc (Maybe SpanIncExc) where intersect = flip intersect
instance Intersect LeftSpaceExc SpanIncExc (Maybe SpanIncExc) where
    intersect ls (SpanIncExc r l) = r `intersect` (l `intersect` ls)
instance Intersect SpanIncExc RightSpaceInc (Maybe SpanIncExc) where intersect = flip intersect
instance Intersect RightSpaceInc SpanIncExc (Maybe SpanIncExc) where
    intersect rs (SpanIncExc r l) = l `intersect` (r `intersect` rs)
instance Intersect SpanIncExc SpanIncExc (Maybe SpanIncExc) where
    intersect s (SpanIncExc r l) = intersect l =<< (r `intersect` s)
instance Intersect (AllOr RightSpaceInc) RightSpaceInc RightSpaceInc   where intersect = allOrIntersect
instance Intersect (AllOr RightSpaceInc) SpanIncExc       (Maybe SpanIncExc) where intersect = allOrIntersectMaybe
instance Intersect (AllOr LeftSpaceExc ) SpanIncExc       (Maybe SpanIncExc) where intersect = allOrIntersectMaybe
instance Intersect RightSpaceInc RightSpaceInc RightSpaceInc where
    intersect (RightSpaceInc a) (RightSpaceInc b) = RightSpaceInc (max a b)
instance Intersect LeftSpaceExc LeftSpaceExc LeftSpaceExc where
    intersect (LeftSpaceExc a) (LeftSpaceExc b) = LeftSpaceExc (min a b)
instance Intersect (AllOr LeftSpaceInc ) (AllOr RightSpaceExc) (Maybe SpanExcInc) where intersect = flip intersect
instance Intersect (AllOr RightSpaceExc) (AllOr LeftSpaceInc)  (Maybe SpanExcInc) where
    intersect (Or rs) (Or ls) = rs `intersect` ls
    intersect allOrRs allOrLs = Just (SpanExcInc allOrRs allOrLs)
instance Intersect (AllOr LeftSpaceExc ) (AllOr RightSpaceInc) (Maybe SpanIncExc) where intersect = flip intersect
instance Intersect (AllOr RightSpaceInc) (AllOr LeftSpaceExc)  (Maybe SpanIncExc) where
    intersect (Or rs) (Or ls) = rs `intersect` ls
    intersect allOrRs allOrLs = Just (SpanIncExc allOrRs allOrLs)
instance Intersect (AllOr LeftSpaceExc) RightSpaceInc (Maybe SpanIncExc) where intersect = flip intersect
instance Intersect RightSpaceInc (AllOr LeftSpaceExc) (Maybe SpanIncExc) where
    intersect rs (Or ls) = rs `intersect` ls
    intersect rs All = Just (SpanIncExc (Or rs) All)
instance Intersect LeftSpaceExc (AllOr RightSpaceInc) (Maybe SpanIncExc) where intersect = flip intersect
instance Intersect (AllOr RightSpaceInc) LeftSpaceExc (Maybe SpanIncExc) where
    intersect (Or rs) ls = rs `intersect` ls
    intersect All ls = Just (SpanIncExc All (Or ls))

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
instance Difference RightSpaceInc RightSpaceInc (Maybe SpanIncExc) where
    difference rsa (RightSpaceInc b) = rsa `intersect` LeftSpaceExc b
instance Difference SpanIncExc SpanIncExc (Maybe SpanIncExc, Maybe SpanIncExc) where
    difference a (SpanIncExc rs ls) = (a `difference` rs, a `difference` ls)
instance Difference SpanIncExc LeftSpaceExc (Maybe SpanIncExc) where
    difference s (LeftSpaceExc b) = s `intersect` (RightSpaceInc b)
instance Difference SpanIncExc RightSpaceInc (Maybe SpanIncExc) where
    difference s (RightSpaceInc b) = s `intersect` (LeftSpaceExc b)
instance Difference a b (Maybe c) => Difference a (AllOr b) (Maybe c) where
    difference _ All = Nothing
    difference a (Or b) = a `difference` b


instance Contains Time SpanExc where
    contains _ _ = False
instance Contains LeftSpaceExc TimeD where
    contains (LeftSpaceExc a) t = t < toTime a
instance Contains RightSpaceInc TimeD where
    contains (RightSpaceInc a) t = t >= toTime a
instance Contains RightSpaceInc Time where
    contains rs t = rs `contains` D_Exactly t
instance Contains SpanExcInc Time where
    contains (SpanExcInc rs ls) t = ls `contains` t && rs `contains` t
instance Contains SpanIncExc Time where
    contains (SpanIncExc rs ls) t = ls `contains` t && rs `contains` t
instance Contains RightSpaceInc RightSpaceInc where
    contains (RightSpaceInc a) (RightSpaceInc b) = a <= b
instance Contains LeftSpaceExc SpanIncExc where
    contains ls (SpanIncExc _ allOrLs) = ls `contains` allOrLs
instance Contains RightSpaceInc SpanIncExc where
    contains rs (SpanIncExc allOrRs _) = rs `contains` allOrRs
instance Contains SpanIncExc SpanIncExc where
    contains (SpanIncExc r l) s = r `contains` s && l `contains` s
instance (Contains a b, IsAllT a) => Contains a (AllOr b) where
    contains a All    = isAllT a
    contains a (Or b) = a `contains` b
instance (Contains a b, IsAllT a) => Contains (AllOr a) b where
    contains All _ = True
    contains (Or a) b = a `contains` b

intersects :: Intersect a b (Maybe c) => a -> b -> Bool
intersects a b = isJust (a `intersect` b)

-- | Covering all of time
instance AllT SpanIncExc where allT = SpanIncExc All All
instance AllT (AllOr a) where allT = All

-- | If the left arg ends exactly on the start of the right arg, return the
-- joined span and the time at which they are joined (such that splitting on
-- that time will give the original spans).
endsOn :: SpanIncExc -> SpanIncExc -> Maybe (SpanIncExc, Time)
endsOn (SpanIncExc allOrRs (Or (LeftSpaceExc hi))) (SpanIncExc (Or (RightSpaceInc lo)) allOrLs)
    | hi == lo  = Just (SpanIncExc allOrRs allOrLs, lo)
endsOn _ _ = Nothing

instantaneous :: SpanIncExc -> Maybe Time
instantaneous (SpanIncExc (Or (RightSpaceInc t)) (Or (LeftSpaceExc t')))
    | t == t' = Just t
instantaneous _ = Nothing

splitSpanAt :: SpanIncExc -> Time -> (Maybe SpanIncExc, Maybe SpanIncExc)
splitSpanAt tspan t = (tspan `intersect` LeftSpaceExc t, tspan `intersect` RightSpaceInc t)

splitSpanAtErr :: SpanIncExc -> Time -> String -> (SpanIncExc, SpanIncExc)
splitSpanAtErr tspan t err = case splitSpanAt tspan t of
    (Just lspan, Just rspan) -> (lspan, rspan)
    _ -> error $ err ++ ": splitSpanAtErr: Found a (Split _ (" ++ show t ++ ") _) but are in span: " ++ show tspan

spanToIncInc :: SpanIncExc -> (TimeX, TimeX)
spanToIncInc (SpanIncExc r l) = (lo, hi)
    where
    lo = case r of
            All -> X_NegInf
            (Or (RightSpaceInc loD)) -> toTime loD
    hi = case l of
            All -> X_Inf
            (Or (LeftSpaceExc hiD)) -> X_JustBefore hiD

instance Arbitrary SpanIncExc where
    arbitrary = arbitrary `suchThatMap` (uncurry spanIncExcMaybe)

instance Arbitrary LeftSpaceExc where arbitrary = LeftSpaceExc <$> arbitrary
instance Arbitrary RightSpaceInc where arbitrary = RightSpaceInc <$> arbitrary
instance Arbitrary a => Arbitrary (AllOr a) where
    arbitrary = frequency [(1, return All), (15, Or <$> arbitrary)]
{-}
-- | Spans that cover all time.
newtype OrderedFullSpans = OrderedFullSpans [SpanIncExc]
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

arbitraryTimeDInSpan :: SpanIncExc -> Gen TimeD
arbitraryTimeDInSpan (SpanIncExc All All) = arbitrary
arbitraryTimeDInSpan (SpanIncExc (Or (RightSpaceInc t)) All)
    = frequency [ (1, return t)
                , (5, sized $ \n -> choose (t, t+(fromIntegral n)))
                ]
arbitraryTimeDInSpan (SpanIncExc All (Or (LeftSpaceExc t)))
    = sized $ \n -> choose (t-(fromIntegral n), t)
arbitraryTimeDInSpan (SpanIncExc (Or (RightSpaceInc lo)) (Or (LeftSpaceExc hi)))
    = frequency [ (1, return lo)
                , (5, choose (lo,hi))
                ]

arbitraryTimeInSpan :: SpanIncExc -> Gen Time
arbitraryTimeInSpan s = arbitraryTimeDInSpan s `suchThatMap` (\td -> let
    t = closestTime td
    in if s `contains` t then Just t else Nothing)

-}

increasingListOf :: Ord a => Gen a -> Gen [a]
increasingListOf xs = fmap head . group . sort <$> listOf xs


data TimeSpan
    -- | DS_Point x ⟹ t < x
    = DS_Point Time
    -- | DS_SpanExc tspan ⟹ t ∈ tspan
    | DS_SpanExc SpanExc
    deriving (Eq, Show)

instance AllT TimeSpan where allT = DS_SpanExc allT

instance Intersect TimeSpan SpanExc (Maybe TimeSpan) where intersect = flip intersect
instance Intersect SpanExc TimeSpan (Maybe TimeSpan) where
    intersect t (DS_Point t')     = DS_Point   <$> intersect t t'
    intersect t (DS_SpanExc tspan)  = DS_SpanExc <$> intersect t tspan

instance Intersect Time TimeSpan (Maybe Time) where intersect = flip intersect
instance Intersect TimeSpan Time (Maybe Time) where
    intersect (DS_Point t)     t' = intersect t t'
    intersect (DS_SpanExc tspan) t  = intersect tspan t

instance Intersect TimeSpan TimeSpan (Maybe TimeSpan) where
    intersect (DS_Point t)     ds = DS_Point <$> intersect t ds
    intersect (DS_SpanExc tspan) ds = intersect tspan ds

instance Contains TimeSpan TimeSpan where
    contains (DS_Point a) (DS_Point b) = contains a b
    contains (DS_Point a) (DS_SpanExc b) = contains a b
    contains (DS_SpanExc a) (DS_Point b) = contains a b
    contains (DS_SpanExc a) (DS_SpanExc b) = contains a b

instance Contains SpanExc TimeSpan where
    contains a (DS_Point b) = contains a b
    contains a (DS_SpanExc b) = contains a b

instance Contains TimeSpan Time where
    contains (DS_Point t) t' = contains t t'
    contains (DS_SpanExc tspan) t = contains tspan t

instance Difference TimeSpan TimeSpan [TimeSpan] where
    difference ts (DS_SpanExc b) = difference ts b
    difference ts (DS_Point t) = difference ts t
instance Difference [TimeSpan] TimeSpan [TimeSpan] where
    difference a b = concatMap (`difference` b) a
instance Difference TimeSpan [TimeSpan] [TimeSpan] where
    difference a bs = foldl' difference [a] bs
instance Difference TimeSpan SpanExc [TimeSpan] where
    difference (DS_Point a) b = fmap DS_Point . maybeToList $ a `difference` b
    difference (DS_SpanExc a) b = concat
        [ l ++ r
        | let (x, y) = a `difference` b
        , let l = case x of
                Nothing -> []
                Just (tspan, t) -> [DS_SpanExc tspan, DS_Point t]
        , let r = case y of
                Nothing -> []
                Just (t, tspan) -> [DS_SpanExc tspan, DS_Point t]
        ]
instance Difference TimeSpan Time [TimeSpan] where
    difference (DS_Point a) b
        | a == b = []
        | otherwise = [DS_Point a]
    difference (DS_SpanExc a) b = DS_SpanExc <$> a `difference` b

instance Pretty TimeSpan where
    pretty = fromString . show


instance Show Span where
    show s = "Span " ++ spanShowCompact s

instance Pretty Span where
    pretty = fromString . spanShowCompact

spanShowCompact :: Span -> String
spanShowCompact (Span lo hi) = loStr ++ "," ++ hiStr
    where
    loStr = case lo of
        Open -> "[←"
        ClosedInc t -> "[" ++ show t
        ClosedExc t -> "(" ++ show t
    hiStr = case hi of
        Open -> "→]"
        ClosedInc t -> show t ++ "]"
        ClosedExc t -> show t ++ ")"