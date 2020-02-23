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

import Data.List (group, sort)
import Data.Maybe (isJust)
import Data.Binary (Binary)
import GHC.Generics (Generic)
import Test.QuickCheck hiding (once)

import Time

data AllOr a
    = All   -- ^ All of time [-Inf, Inf]
    | Or !a  -- ^ Just that a.
    deriving stock (Show, Generic) -- NOT Ord
    deriving anyclass (Binary)

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

-- [[ Span l r ]] = l `intersect` r
-- Non empty
data SpanExc
    = SpanExc
        !(AllOr RightSpaceExc) -- ^ Time span left  bound Exclusive. All == Inclusive -Inf
        !(AllOr LeftSpaceExc)  -- ^ Time span right bound Exclusive. All == !Inclusive! Inf
    deriving stock (Eq, Generic) -- NOT Ord
    deriving anyclass (Binary)

instance Show SpanExc where
    show (SpanExc allOrR allOrL) = "SpanExc [" ++ rt  ++ " " ++ lt ++ "]"
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
        Nothing -> error "spanIncExc: lo >= hi"
        Just x -> x

-- Inclusive start Exclusive end span.
-- Nothing if the input times are not strictly increasing.
spanExcMaybe :: Maybe Time -> Maybe Time -> Maybe SpanExc
spanExcMaybe lo hi = (maybe All (Or . RightSpaceExc) lo) `intersect`
                        (maybe All (Or . LeftSpaceExc) hi)

spanExcMaxT :: SpanExc -> TimeX
spanExcMaxT (SpanExc _ All) = X_Inf
spanExcMaxT (SpanExc _ (Or (LeftSpaceExc t))) = X_JustBefore t

class Intersect a b c | a b -> c where
    intersect :: a -> b -> c

-- a `difference` b == a `intersect` (invert b)
class Difference a b c | a b -> c where
    difference :: a -> b -> c

class NeverAll a
instance NeverAll LeftSpaceExc
instance NeverAll RightSpaceExc

class Contains a b where
    contains :: a -> b -> Bool

-- | Covering all of time
class AllT a where allT :: a
instance AllT SpanExc where allT = SpanExc All All

class IsAllT a where isAllT :: a -> Bool
instance IsAllT LeftSpaceExc where isAllT _ = False
instance IsAllT RightSpaceExc where isAllT _ = False

instance Intersect LeftSpaceExc RightSpaceExc (Maybe SpanExc) where intersect = flip intersect
instance Intersect RightSpaceExc LeftSpaceExc (Maybe SpanExc) where
    intersect r@(RightSpaceExc lo) l@(LeftSpaceExc hi)
        | lo < hi = Just (SpanExc (Or r) (Or l))
        | otherwise = Nothing
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
instance Intersect LeftSpaceExc LeftSpaceExc LeftSpaceExc where
    intersect (LeftSpaceExc a) (LeftSpaceExc b) = LeftSpaceExc (min a b)
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


-- instance Contains LeftSpaceExc TimeD where
--     contains (LeftSpaceExc a) t = t < a
-- instance Contains RightSpaceExc TimeD where
--     contains (RightSpaceExc a) t = t > a
instance Contains LeftSpaceExc Time where
    contains (LeftSpaceExc ls) t = t < ls
instance Contains RightSpaceExc Time where
    contains (RightSpaceExc rs) t = t > rs
instance Contains SpanExc Time where
    contains (SpanExc rs ls) t = ls `contains` t && rs `contains` t
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


--
-- Time Span stuff
--

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

instance NeverAll LeftSpace
instance NeverAll RightSpace

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
instance AllT Span where allT = Span All All
instance AllT (AllOr a) where allT = All

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