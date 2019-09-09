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
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module Time
    ( Time
    , BehTime (..)
    , minTimeBehTime
    , delayBehTime
    ) where

type Time = Integer -- TODO Int64? nanoseconds?

data BehTime
    = Exactly   { btTime :: Time }
    | JustAfter { btTime :: Time }
    | Inf
    deriving (Show, Eq)

minTimeBehTime :: Time -> BehTime -> Time
minTimeBehTime t (Exactly bt)   = min bt t
-- TODO this is a bit inacurate. We may be off by an infinitesimal amount of time :-(
minTimeBehTime t (JustAfter bt) = min bt t
minTimeBehTime t Inf            = t

delayBehTime :: BehTime -> BehTime
delayBehTime (Exactly t)   = JustAfter t
delayBehTime (JustAfter t) = JustAfter t
delayBehTime Inf           = Inf

instance Ord BehTime where
    compare Inf Inf = EQ
    compare Inf _ = GT
    compare _ Inf = LT
    compare a b = case btTime a `compare` btTime b of
        LT -> LT
        EQ -> case (a, b) of
            (Exactly   _, Exactly   _) -> EQ
            (JustAfter _, JustAfter _) -> EQ
            (Exactly   _, JustAfter _) -> LT
            (JustAfter _, Exactly   _) -> GT
            (Inf, _) -> error "Impossible"
            (_, Inf) -> error "Impossible"
        GT -> GT
