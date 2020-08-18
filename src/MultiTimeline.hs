{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wincomplete-uni-patterns #-}

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | Timeline of facts for a value.
module MultiTimeline where

import qualified Data.List as L
import Prelude hiding (lookup, null)

-- import Time
import Time
import TimeSpan

-- | A timeline is a map from time to values where values may be set on spans of
-- time. Implemented as a list of Timelines. We use multiple timelines when we
-- cannot avoid overlap. This will give poor performance, linear in the maximum
-- amount of overlap, but we hope to deal with relativelly small amounts of
-- overlap. Invariant: all Timelines are non-empty.
data MultiTimeline a = MultiTimeline [(Span, a)] -- TODO make this efficient

empty :: MultiTimeline a
empty = MultiTimeline []

null :: MultiTimeline a -> Bool
null (MultiTimeline []) = True
null (MultiTimeline _) = False

singleton :: Span -> a -> MultiTimeline a
singleton s a = MultiTimeline [(s, a)]

singletonT :: Time -> a -> MultiTimeline a
singletonT t a = singleton (timeToSpan t) a

singletonTSpan :: TimeSpan -> a -> MultiTimeline a
singletonTSpan ts a = singleton (timeSpanToSpan ts) a

deleteVal :: Eq a => a -> MultiTimeline a -> MultiTimeline a
deleteVal a (MultiTimeline els) = MultiTimeline (L.deleteBy (\x y -> snd x == snd y) (undefined,a) els)

-- | Things that intersect the span in arbitrary order. TODO This could work
-- efficiently by traversing elements from both ends of the span travering from
-- both ends of
select :: Span -> MultiTimeline a -> MultiTimeline a
select s (MultiTimeline els) = MultiTimeline (filter (intersects s . fst) els)

elems :: forall a . MultiTimeline a -> [a]
elems (MultiTimeline els) = snd <$> els

-- fromList :: [(TimeSpan, a)] -> MultiTimeline a
-- fromList = foldl' (\tl (timeSpan, value) -> insert timeSpan value tl) empty

insert :: Span -> a -> MultiTimeline a -> MultiTimeline a
insert s a (MultiTimeline el) = MultiTimeline ((s,a):el)

insertTimeSpan :: TimeSpan -> a -> MultiTimeline a -> MultiTimeline a
insertTimeSpan tts = insert (timeSpanToSpan tts)


{-
newtype MultiTimeline a = MultiTimeline [Timeline () a]

empty :: MultiTimeline a
empty = MultiTimeline []

null :: MultiTimeline a -> Bool
null (MultiTimeline tls) = case tls of
    [] -> True
    _ -> False

singletonOcc :: Time -> a -> MultiTimeline a
singletonOcc tts a = MultiTimeline [T.singletonOcc () tts a]

singletonNoOcc :: TimeSpan -> MultiTimeline a
singletonNoOcc tts = MultiTimeline [T.singletonNoOcc () tts]

select :: Span -> MultiTimeline a -> MultiTimeline a
select s (MultiTimeline ts) = MultiTimeline
    $ filter (not . T.null)
    $ map (T.select s) ts

elems :: forall a . MultiTimeline a -> [Either TimeSpan (Time, a)]
elems (MultiTimeline mt) = reduce es
    where
    es :: [[Either TimeSpan (Time, a)]]
    es = fmap snd . T.elems <$> mt
    merge :: [Either TimeSpan (Time, a)] -> [Either TimeSpan (Time, a)] -> [Either TimeSpan (Time, a)]
    reduce :: [[Either TimeSpan (Time, a)]] ->  [Either TimeSpan (Time, a)]
    reduce [] =

-- fromList :: [(TimeSpan, a)] -> MultiTimeline a
-- fromList = foldl' (\tl (timeSpan, value) -> insert timeSpan value tl) empty

-- insert :: TimeSpan -> a -> MultiTimeline a -> MultiTimeline a
-- insert tts a (MultiTimeline tls) = MultiTimeline (go tls)
--     where
--     go [] = [T.singleton tts a]
--     go (t:ts) = case T.tryInsert tts a t of
--         Nothing -> t : go ts
--         Just t' -> t' : ts

-}

todo :: a
todo = error "TODO MultiTimeline"