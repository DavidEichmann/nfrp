{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module GateRep where

import Time

-- | `dropUntilTime 3 [(4,_), (3,_), (2,_), (1,_)]
--                 == [       (3,_), (2,_), (1,_)]
dropUntilTime :: (ToTime t1 TimeDI, ToTime t2 TimeDI) => t1 -> [(t2, a)] -> [(t2, a)]
dropUntilTime t = dropWhile ((< tDI) . toTime . fst)
    where
    tDI :: TimeDI
    tDI = toTime t


-- | A behavior style map. Represents a partial mapping from time to value (see lookupBMap).
newtype BMap a = BMap [(TimeDI, Maybe a)]
    -- ^ [(t, aMay: value (if one is known at time midT onwards))]
    -- You can imagine there is an implicit (Nothing, -Infintiy) at the end of the list.
    -- List is in reverse chronological order i.e. for all indexes, i:
    --   t(i) > t(i+1)

-- | This defines the denotation of BMap
-- Lookup the value of a behavior at a given time.
lookupBMap :: TimeDI -> BMap a -> Maybe a
lookupBMap t (BMap allXs) = go allXs
    where
    go [] = Nothing
    go ((t_i, aMay_i):xs)
        | t >= t_i  = aMay_i
        | otherwise = go xs


-- | An event style map. Represents a partial mapping from time to events (see lookupEMap).
data EMapEl a
    = Start -- ^ event's are known from here onwards.
    | Stop  -- ^ event's are known from here onwards.
    | Occur a -- ^ Event occurs here
newtype EMap a = EMap [(Time, EMapEl a)]
    -- ^ [(aMay: value (if one is known at time midT onwards), t)]
    -- You can imagine there is an implicit (Nothing, -Infintiy) at the end of the list.
    -- List is in reverse chronological order i.e. for all indexes, i:
    --   t(i) > t(i+1)
