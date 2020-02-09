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

-- TODO specialize maxT/minT to TimeDI and rename TimeDI to just Time'.
-- now the bounds of event/behavior GateReps may allow for Inf/JustAfter,
-- but events cannot be delayed nor occur at infinity

-- | This is the representation of the values of a gate throughout a closed interval of time (including the start and end times).
data GateRep time a = GateRep
    { grepMaxT    :: TimeDI         -- ^ grepChanges is commited up to this time (inclusive).
    , grepChanges :: [(time, a)]    -- ^ Value changes in reverse chronolgical order. All times, t, are grepMinT <= t <= grepMaxT.
    , grepMinT    :: TimeD          -- ^ grepChanges is commited starting at this time (inclusive).
    } deriving (Show, Functor)

instance Ord time => Semigroup (GateRep time a) where
    (GateRep maxTL usL minTL) <> (GateRep maxTR usR minTR)
        | toTime minTL /= delayTime maxTR
            = error $ "Cannot concatenate gates with non-continuous times: "
                    ++ ". Requires [a,b] [c,d] where a >= b, b == c+, c >= d"
        | otherwise = GateRep maxTL (usL ++ usR) minTR


-- | `dropUntilTime 3 [(4,_), (3,_), (2,_), (1,_)]
--                 == [       (3,_), (2,_), (1,_)]
dropUntilTime :: (ToTime t1 TimeDI, ToTime t2 TimeDI) => t1 -> [(t2, a)] -> [(t2, a)]
dropUntilTime t = dropWhile ((< tDI) . toTime . fst)
    where
    tDI :: TimeDI
    tDI = toTime t

