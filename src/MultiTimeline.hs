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

import Prelude hiding (lookup, null)
-- import Data.Map.Strict (Map)
-- import qualified Data.Map.Strict as M
-- import Data.Maybe (maybeToList)

-- import Time
import Timeline (Timeline)
import qualified Timeline as T
import Time
import TimeSpan

-- | A timeline is a map from time to values where values may be set on spans of
-- time. Implemented as a list of Timelines. We use multiple timelines when we
-- cannot avoid overlap. This will give poor performance, linear in the maximum
-- amount of overlap, but we hope to deal with relativelly small amounts of
-- overlap. Invariant: all Timelines are non-empty.
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


todo :: a
todo = error "TODO MultiTimeline"