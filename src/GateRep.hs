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
import Data.List (find, foldl', group, nub, partition)
import Data.Maybe (fromJust, fromMaybe, isJust)
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
-- TODO with our rep starting at -Inf instead of 0 we dont need to insert a new intial value!
-- This seems fishy.
delay :: forall a . Behavior a -> Behavior a
delay top = go top Nothing
    where
    go :: Behavior a -> Maybe TimeD -> Behavior a
    go (Split left t right) hiM =
        let
        t' = delayTime t
        -- If there is already a next value at the delayed time, then discard the right value.
        in if Just t' == hiM
            then go left (Just t')
            else Split (go left (Just t')) t' (go right hiM)
    go v _ = v

-- ^ No Maybe! because in this system, it will just block if the value is unknown.
sampleB :: Behavior a -> Time -> a
sampleB b t = go b
    where
    tdi = D_Exactly t
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


--
-- Explicitly partial versions of Behavior/Event
--

data MaybeKnown a = Unknown | Known a
type BehaviorPart a = Behavior (MaybeKnown a)
newtype EventPart a = EventPart { unEventPart :: BehaviorPart (Occ a) }

-- | Assumes a finite input list.
-- Errors is there are overlapping time spans.
listToEPartErr :: forall a . [(Span, [(Time, a)])] -> EventPart a
listToEPartErr spans = let
    knownBs :: [BehaviorPart (Occ a)]
    knownBs = [ let Event occsB = listToE occs
                    knowlage = Known <$> occsB
                    unknown = Value Unknown
                 in case find (not . (tspan `contains`)) (fst <$> occs) of
                        Just errT -> error $ "listToEPartErr: found event at time (" ++ show errT ++ ") not in span (" ++ show tspan ++ ")"
                        Nothing -> case tspan of
                            Span All All -> knowlage
                            Span All (Or (LeftSpace t)) -> Split knowlage t unknown
                            Span (Or (RightSpace t)) All -> Split unknown t knowlage
                            Span (Or (RightSpace tlo)) (Or (LeftSpace thi)) -> Split (Split unknown tlo knowlage) thi unknown
            | (tspan, occs) <- spans
            ]
    in EventPart (foldl' unionBP (pure Unknown) knownBs)

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
                then []
                else let
                    (lastLSpan,lastLB) = last spansL
                    (headRSpan,headRB) = head spansR
                    in case lastLSpan `endsOn` headRSpan of
                        Just (midSpan, midT) ->  init spansL ++ [(midSpan, Split lastLB midT headRB)] ++ tail spansR
                        Nothing -> spansL ++ spansR
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
            partSpans :: [Span] <- _knownSpansE part
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


--
-- Time Span stuff
--

data AllOr a
    = All   -- ^ All of time [-Inf, Inf]
    | Or a  -- ^ Just that a.
    deriving (Show) -- NOT Ord

-- Half spaces
newtype LeftSpace  = LeftSpace  TimeD   -- ^ [[ LeftSpace  t' ]] = { t | t <  t' }
    deriving (Show,Eq,Ord)
newtype RightSpace = RightSpace TimeD   -- ^ [[ RightSpace t' ]] = { t | t >= t' }
    deriving (Show,Eq,Ord)


-- [[ Span l r ]] = l `intersect` r
data Span
    = Span
        (AllOr RightSpace) -- ^ Time span left  bound Inclusive. All == Inclusive -Inf
        (AllOr LeftSpace)  -- ^ Time span right bound Exclusive. All == !Inclusive! Inf
    deriving (Show) -- NOT Ord


class Intersect a b c | a b -> c where
    intersect :: a -> b -> c

instance Intersect RightSpace LeftSpace (Maybe Span) where intersect = flip intersect
instance Intersect LeftSpace RightSpace (Maybe Span) where
    intersect l@(LeftSpace lo) r@(RightSpace hi)
        | lo < hi = Just (Span (Or r) (Or l))
        | otherwise = Nothing
instance Intersect Span LeftSpace (Maybe Span) where intersect = flip intersect
instance Intersect LeftSpace Span (Maybe Span) where
    intersect ls (Span r l) = r `intersect` (l `intersect` ls)
instance Intersect Span RightSpace (Maybe Span) where intersect = flip intersect
instance Intersect RightSpace Span (Maybe Span) where
    intersect rs (Span r l) = _ -- intersect l =<< (r `intersect` rs)
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
    difference a b@(Span rs ls) = (a `difference` rs, a `difference` ls)
instance Difference Span LeftSpace (Maybe Span) where
    difference (Span r l) _ = _
instance Difference Span RightSpace (Maybe Span) where
    difference (Span r l) _ = _
instance Difference a b (Maybe c) => Difference a (AllOr b) (Maybe c) where
    difference _ All = Nothing
    difference a (Or b) = a `difference` b

class NeverAll a
instance NeverAll LeftSpace
instance NeverAll RightSpace

class Contains a b where
    contains :: a -> b -> Bool

instance Contains LeftSpace Time where
    contains (LeftSpace a) t = D_Exactly t < a
instance Contains RightSpace Time where
    contains (RightSpace a) t = D_Exactly t >= a
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
    contains = _

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
    _ -> error $ err ++ ": Found a (Split _ (" ++ show t ++ ") _) but are in span: " ++ show tspan
