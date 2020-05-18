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

import Control.Concurrent.STM
import Control.Monad (ap, liftM)
import Data.Map (Map, (!?))
import qualified Data.Map as M
import Data.Void (Void)
import Data.Coerce
import qualified StmContainers.Map as SM
import Unsafe.Coerce

import Theory
  ( DerivationSpan(..)
  , EIx(..)
  , EventFact(..)
  , Inputs
  , MaybeOcc
  , SomeDerivation(..)
  , SomeEIx(..)
  , SomeEventFact(..)
  , factTSpan
  )
import Time
import TimeSpan

type Coerced = Void

-- | Efficient implementation of a space that is evaluated lazily by concurrent
-- "derivations" that depends on other values in the space. This data stores all
-- known facts and active derivations.
data Reactor = Reactor
  { reactorFacts'      :: SM.Map SomeEIx
      ( TVar (Maybe (EventFact Coerced)) -- Span fact starting at -Inf
      , TVar
        ( Map Time -- key is lo time
          ( TVar (Maybe (EventFact Coerced)) -- Point Fact
          , TVar (Maybe (EventFact Coerced)) -- Span Fact
          )
        )
      )
    -- ^ Facts with no overlap (point, span) indexed by:
    --   * Event index
    --   * event lo time (gives a list of point time facts)
    -- Note that point fact must be Nothing at lo time None (we don't allow events at -Inf)

  , reactorReactions :: SM.Map SomeEIx
      ( TVar (Map Time [Reaction ()]) -- Span reactions starting at -Inf
      , TVar
        ( Map Time -- key is lo time
          ( TVar ([MaybeOcc Coerced -> Reaction ()])
          , TVar (Map Time [Reaction ()]) -- key is hi time
          , TVar ([Reaction ()]) -- Reactions with hi time of Inf
          )
        )
      )
    -- ^ Active reactions indexed by their current dependency:
    --   * Dependency event index
    --   * lo time (point time for derivations that depend on a point)
    --   * hi time
    -- Note that point Reactions must be empty at lo time None (we don't allow events at -Inf)
  }

newtype Reaction a = Reaction (Reactor -> STM ([SomeEventFact], [Reaction ()], Either a (Reaction a)))

data SomeReaction = forall a . SomeReaction (Reaction a)

instance Functor Reaction where
  fmap = liftM
instance Applicative Reaction where
  pure a = Reaction $ \_ -> pure ([], [], Right (pure a))
  (<*>) = ap
instance Monad Reaction where
  (Reaction go) >>= ab = Reaction $ \reactor -> do
    (facts, newRs, cont) <- go reactor
    return
      ( facts
      , newRs
      , Right $ case cont of
          Left a -> ab a
          Right aR -> aR >>= ab
      )

-- | Lookup an event at a given time.
lookupER :: Time -> EIx a -> Reaction (MaybeOcc a)
lookupER t eix = do
  fact <- lookupEFactR t eix
  return $ case fact of
    FactMayOcc _ _ occMay -> occMay
    FactNoOcc _ _ -> Nothing

-- | Lookup the event at a given time. This matches the `lookupE` denotation in
-- the Reaction Monad.
lookupEFactR :: forall a . Time -> EIx a -> Reaction (EventFact a)
lookupEFactR t eix = Reaction $ \(Reactor allFacts _) -> do
  let seix = SomeEIx eix
  -- Get facts for this event, eix.
  factsEMay <- SM.lookup seix allFacts
  case factsEMay of
    Nothing -> retry
    Just (negInfFactMayT, factsT) -> do
      -- Check if the -Inf span fact exists/contains t.
      negInfFactMay <- do
        negInfFactMay <- readTVar negInfFactMayT
        return $ case negInfFactMay of
          Just negInfFact | factTSpan negInfFact `contains` t -> Just negInfFact
          _ -> Nothing
      case negInfFactMay of
        -- Use the -Inf span fact
        Just negInfFact -> return ([], [], Left (doCoerce negInfFact))
        -- Either the -Inf span fact isn't known or doesn't contain t. Look at
        -- the rest of the facts.
        Nothing -> do
          -- No -Inf fact, so look in factsT
          facts <- readTVar factsT
          case M.lookupLE t facts of
            Just (t', (pointFactMayT, spanFactMayT))
              | t == t'
              -> do
                pointFactMay <- readTVar pointFactMayT
                case pointFactMay of
                  Nothing -> retry
                  Just pointFact -> return ([], [], Left (doCoerce pointFact))
              | otherwise
              -> do
                spanFactMay <- readTVar spanFactMayT
                case spanFactMay of
                  Just spanFact | factTSpan spanFact `contains` t
                    -> return ([], [], Left (doCoerce spanFact))
                  _ -> retry
            Nothing -> retry
  where
  doCoerce :: EventFact Coerced -> EventFact a
  doCoerce = unsafeCoerce

{-
-- | Look up known and unknown facts within a span. Retries if there are no
-- facts. This is like `Theory.spanLookupEFacts`.
lookupESpanR
  :: SpanExc
  -> EIx a
  -> Reaction ([(DerivationSpan, Maybe a)], [DerivationSpan])
    -- ^ ( Known values about the given event
    --   , unknown times and time spans )
    --   The union of these times and time spans should exactly
    --   equal the input time span.
lookupESpanR tspan eix = Reaction $ \(Reactor allFacts _) -> do
  let seix = SomeEIx eix
  factsEMay <- SM.lookup seix allFacts
  case factsEMay of
    Nothing -> retry
    Just facts -> do
      let lo = spanExcJustBefore tspan
      let hi = spanExcJustAfter tspan
      case facts !? t of
        Just (Just fact, _) -> return ([], [], Left (unsafeCoerce fact))
        _ -> retry
  where
  doCoerce :: EventFact Coerced -> EventFact a
  doCoerce = unsafeCoerce

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

-- lookupEReactor :: forall a . Coercible a Void => Time -> EIx a -> Reactor -> MaybeKnown (MaybeOcc a)
-- lookupEReactor t eix (Reactor fs _) = MaybeKnown $ do
--   loTimeToFacts :: Map Time (Maybe (EventFact a), Maybe (EventFact a))
--     <- coerce <$> (fs !? SomeEIx eix)
--   loTimeToFacts
--   _

-}