{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}

module Reactor where

import Control.Monad (ap)
import Data.Map (Map, (!?))
import Data.Void (Void)
import Data.Coerce
import Unsafe.Coerce

import Theory
import Time
import TimeSpan

type Coerced = Void

-- | Efficient implementation of a space that is evaluated lazily by concurrent
-- "derivations" that depends on other values in the space. This data stores all
-- known facts and active derivations.
data Reactor = Reactor
  { reactorFacts'      :: Map SomeEIx (Map Time (Maybe (EventFact Coerced), Maybe (EventFact Coerced)))
    -- ^ Facts with no overlap (point, span) indexed by:
    --   * Event index
    --   * event lo time (gives a list of point time facts)
  , reactorDerivations :: Map SomeEIx (Map Time ([MaybeOcc Coerced -> Reaction ()], Map Time [SomeDerivation]))
    -- ^ Active derivations indexed by their current dependency:
    --   * Dependency event index
    --   * lo time (point time for derivations that depend on a point)
    --   * hi time
  }

-- | The monad on which Derivation is implemented.
data Reaction a
  = forall b . RLookupEPoint Time    (EIx b) (MaybeOcc b -> Reaction a)
  | forall b . RLookupESpan  SpanExc (EIx b) (([(DerivationSpan, Maybe b)], [DerivationSpan]) -> Reaction a)
  | RYield SomeEventFact (Reaction a)
  | RFork (Reaction ()) (Reaction a)
  | RPure a

deriving instance Functor Reaction

instance Applicative Reaction where
  pure = return
  (<*>) = ap

instance Monad Reaction where
  return = RPure
  a >>= b = case a of
    RLookupEPoint t     eix cont -> RLookupEPoint t     eix ((>>= b) . cont)
    RLookupESpan  tspan eix cont -> RLookupESpan  tspan eix ((>>= b) . cont)
    RYield someEventFact c -> RYield someEventFact (c >>= b)
    RFork c d -> RFork c (d >>= b)
    RPure c -> b c

-- | Lookup the event at a given time. This matches the `lookupE` denotation in
-- the Reaction Monad.
lookupER :: Time -> EIx a -> Reaction (MaybeOcc a)
lookupER t eix = RLookupEPoint t eix return

lookupESpanR
  :: SpanExc
  -> EIx a
  -> Reaction ([(DerivationSpan, Maybe a)], [DerivationSpan])
    -- ^ ( Known values about the given event
    --   , unknown times and time spans )
    --   The union of these times and time spans should exactly
    --   equal the input time span.
lookupESpanR tspan eix = RLookupESpan tspan eix return

yield :: EIx a -> EventFact a -> Reaction ()
yield eix fact = RYield (SomeEventFact eix fact) (return ())

forkR :: Reaction () -> Reaction ()
forkR r = RFork r (return ())

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

newReactor :: Inputs -> Reactor
newReactor = _

addFact :: EventFact a -> Reactor -> Reactor
addFact = _

addPointFact :: Time -> Maybe a -> Reactor -> Reactor
addPointFact t aMay = addFact (FactMayOcc [] t aMay)

addNoOccSpanFact :: Maybe Time -> Maybe Time -> Reactor -> Reactor
addNoOccSpanFact lo hi = addFact (FactNoOcc [] (spanExc lo hi))

lookupEReactor :: forall a . Coercible a Void => Time -> EIx a -> Reactor -> MaybeKnown (MaybeOcc a)
lookupEReactor t eix (Reactor fs _) = MaybeKnown $ do
  loTimeToFacts :: Map Time (Maybe (EventFact a), Maybe (EventFact a))
    <- coerce <$> (fs !? SomeEIx eix)
  loTimeToFacts
  _
