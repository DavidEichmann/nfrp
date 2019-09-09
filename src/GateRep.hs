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

module GateRep where

data GateRep time a = GateRep
    { grepMaxT :: time              -- ^ grepChanges is commited up to this time.

    -- TODO it seems better to specify a start time. At the moment this is implicitelly 0 in the live circuit, or "the current maxT" when dealing with updates. We leave it up to the programmer to use (<>) correctly i.e. `updates <> currentRep` makes sense.
    -- , grepMinT :: time              -- ^ grepChanges is commited starting at this time.
    , grepChanges :: [(time, a)]    -- ^ Value changes in reverse chronolgical order. All times are <= grepMaxT.
    } deriving Show

-- | `dropUntilTime 3 [(4,_), (3,_), (2,_), (1,_)]
--                 == [       (3,_), (2,_), (1,_)]
dropUntilTime :: Ord t => t -> [(t, a)] -> [(t, a)]
dropUntilTime t = dropWhile ((> t) . fst)

