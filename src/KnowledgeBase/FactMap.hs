{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wincomplete-uni-patterns #-}

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module KnowledgeBase.FactMap where

import qualified Data.Map as Map
import Data.Map (Map, (!?))

import Time
import TimeSpan

data FactSpanE
    = FSE_Point Time
    | FSE_Span SpanExc
data FactSpanB
    = FSB_Init
    | FSB_Point Time
    | FSB_Span SpanExc

type KeyB game a = forall e b . game e e b -> b a
type KeyE game a = forall e b . game e e b -> e a
data Key game a
    = KeyB (KeyB game a)
    | KeyE (KeyE game a)

-- Facts contain either Change/NoChange facts, or solid values
newtype KBFactsE a = KBFactsE           (Map TimeX (FactE a))
data    KBFactsB a = KBFactsB (Maybe a) (Map TimeX (FactBC a))

data Fact game
    = forall a . FactB (KeyB game a) (FactB a)
    | forall a . FactE (KeyE game a) (FactE a)

data FactB a
    = Init a
    | FactB_Change (FactBC a)

data FactBC a
    = Change Time (Maybe a)
    | NoChange SpanExc

data FactBVal a
    = InitVal a
    | FactBVal_Change (FactBCVal a)

data FactBCVal a
    = ValueBChange Time a
    | ValueBNoChange SpanExc a

data Occ a = Occ a | NoOcc

data FactE a
    = FactOcc Time (Occ a)
    | FactNoOcc SpanExc

getFactBValSpan :: FactBCVal a -> Either Time SpanExc
getFactBValSpan (ValueBChange t _) = Left t
getFactBValSpan (ValueBNoChange tspan _) = Right tspan
