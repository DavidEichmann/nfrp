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
{-
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

type ReactorFacts a =
  ( TVar (Maybe (EventFact a)) -- Span fact starting at -Inf
  , TVar
    ( Map Time -- key is lo time
      ( TVar (Maybe (EventFact a)) -- Point Fact
      , TVar (Maybe (EventFact a)) -- Span Fact
      )
    )
  )

-- | Efficient implementation of a space that is evaluated lazily by concurrent
-- "derivations" that depends on other values in the space. This data stores all
-- known facts and active derivations.
data Reactor = Reactor
  { reactorFacts'      :: SM.Map SomeEIx (ReactorFacts Coerced)
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

-- | Get all facts about an event. Never retries.
factsE :: EIx a -> Reaction (ReactorFacts a)
factsE eix = Reaction $ \ractor -> do
  rfa <- factsESTM eix ractor
  return ([], [], Left rfa)

-- | Get all facts about an event. Never retries.
factsESTM :: EIx a -> Reactor -> STM (ReactorFacts a)
factsESTM eix (Reactor facts _) = do
  fsMay <- SM.lookup (SomeEIx eix) facts
  case fsMay of
    Nothing -> do
      initSpanFact <- newTVar Nothing
      otherFacts <- newTVar M.empty
      let value = (initSpanFact, otherFacts)
      SM.insert value (SomeEIx eix) facts
      return (doCoerce value)
    Just fs -> return (doCoerce fs)
  where
  doCoerce :: ReactorFacts Coerced -> ReactorFacts a
  doCoerce = unsafeCoerce

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
lookupEFactR t eix = Reaction $ \reactor -> do
  -- Get facts for this event, eix.
  (negInfFactMayT, factsT) <- factsESTM eix reactor
  -- Check if the -Inf span fact exists/contains t.
  negInfFactMay <- do
    negInfFactMay <- readTVar negInfFactMayT
    return $ case negInfFactMay of
      Just negInfFact | factTSpan negInfFact `contains` t -> Just negInfFact
      _ -> Nothing
  case negInfFactMay of
    -- Use the -Inf span fact
    Just negInfFact -> return ([], [], Left negInfFact)
    -- Either the -Inf span fact isn't known or doesn't contain t. Look at
    -- the rest of the facts.
    Nothing -> do
      -- No -Inf fact, so look in factsT
      (t', (pointFactMayT, spanFactMayT)) <- untilJust (M.lookupLE t <$> readTVar factsT)
      if t == t'
      then do
        pointFact <- untilJust $ readTVar pointFactMayT
        return ([], [], Left pointFact)
      else do
        spanFact <- untilJust $ readTVar spanFactMayT
        check (factTSpan spanFact `contains` t)
        return ([], [], Left spanFact)

-- -- | Look up known and unknown facts within a span. Retries if there are no
-- -- facts. This is like `Theory.spanLookupEFacts`.
-- lookupESpanR
--   :: SpanExc
--   -> EIx a
--   -> Reaction ([(DerivationSpan, Maybe a)], [DerivationSpan])
--     -- ^ ( Known values about the given event
--     --   , unknown times and time spans )
--     --   The union of these times and time spans should exactly
--     --   equal the input time span.
-- lookupESpanR tspan eix = do
--   scanRightIncFacts (spanExcJustBefore tspan)
--   (initFactSpanT, factsT) <- factsE eix
--   let
--     -- All go functions start at a time and scan toward input span's end time.

--     -- Scan includes lo
--     goPoint :: Time -> Reaction ([(DerivationSpan, Maybe a)], [DerivationSpan])
--     goPoint lo = _

--     -- scan excludes lo
--     goSpan :: Time -> Reaction ([(DerivationSpan, Maybe a)], [DerivationSpan])
--     goSpan lo = _

--   case spanExcJustBefore tspan of
--       Just lo -> goSpan lo
--       Nothing -> do
--         facts ?! _
--         return _

newtype LazyRList a = LazyRList { unLazyRList :: Reaction (Maybe (a, LazyRList a)) }
-- | Look up known facts from left to right starting from the given
-- time (inclusive). This doesn't crop the facts, so the first fact may start before the
-- input time.
instance Semigroup (LazyRList a) where
  a <> b = LazyRList $ do
    elMay <- unLazyRList a
    case elMay of
      Nothing -> return Nothing
      Just (el, a') -> return (Just (el, a' <> b))

scanRightIncFacts
  :: Maybe Time -- Nothing means -Inf
  -> EIx a
  -> LazyRList (EventFact a)
    -- ^ ( Known values about the given event (Left)
    --   , unknown times and time spans (Right))
scanRightIncFacts tMay eix = LazyRList $ do
  (initFactMayT, factsT) <- factsE eix
  initFactMay <- liftSTM $ readTVar initFactMayT
  case tMay of
    -- Start time is -Inf, so just return all facts.
    Nothing -> do
      let factsLRL = LazyRList $ do
                facts <- liftSTM $ readTVar factsT
                unLazyRList (elems' facts)
      case initFactMay of
        Just initFact -> return $ Just (initFact, factsLRL)
        Nothing -> unLazyRList factsLRL
    Just t -> do
      let factsLRL = LazyRList $ do
                facts <- liftSTM $ readTVar factsT
                let facts' = M.dropWhileAntitone (< t) facts
                unLazyRList (elems' facts')
      case initFactMay of
        Just initFact
          | factTSpan initFact `contains` t
          -> return $ Just (initFact, factsLRL)
        _ -> unLazyRList factsLRL
  where
  elems'
    :: Map Time (TVar (Maybe (EventFact a)), TVar (Maybe (EventFact a)))
    -> LazyRList (EventFact a)
  elems' = go . concatMap (\(a,b) -> [a,b]) . M.elems
    where
    go [] = LazyRList (return Nothing)
    go (x:xs) = LazyRList $ do
      factMay <- liftSTM $ readTVar x
      case factMay of
        Nothing -> unLazyRList (go xs)
        Just fact -> return $ Just (fact, go xs)

scanRightFacts
  :: Bool -- True to include the given time.
  -> Maybe Time -- Nothing means -Inf
  -> EIx a
  -> LazyRList (EventFact a)
    -- ^ ( Known values about the given event (Left)
    --   , unknown times and time spans (Right))
scanRightFacts inclusive tMay eix = LazyRList $ do
  (initFactMayT, factsT) <- factsE eix
  initFactMay <- liftSTM $ readTVar initFactMayT
  case tMay of
    -- Start time is -Inf, so just return all facts.
    Nothing -> do
      let factsLRL = LazyRList $ do
                facts <- liftSTM $ readTVar factsT
                unLazyRList (elems' All facts)
      case initFactMay of
        Just initFact -> return $ Just (initFact, factsLRL)
        Nothing -> unLazyRList factsLRL
    Just t -> do
      let factsLRL = LazyRList $ do
                facts <- liftSTM $ readTVar factsT
                let (facts'lo, facts'hi) = M.spanAntitone (< t) facts
                let facts' = case M.lookupMax facts'lo of
                      Nothing -> facts'hi
                      Just (k, v) -> M.insert k v facts'hi
                unLazyRList (elems' ((RightSpaceExc t)) facts')
      case initFactMay of
        Just initFact
          | factTSpan initFact `contains` t
          -> return $ Just (initFact, factsLRL)
        _ -> unLazyRList factsLRL
  where
  elems'
    :: Intersect s DerivationSpan (Maybe i)
    => s
    -> Map Time (TVar (Maybe (EventFact a)), TVar (Maybe (EventFact a)))
    -> LazyRList (EventFact a)
  elems' s = go . concatMap (\(a,b) -> [a,b]) . M.elems
    where
    -- With check if after t
    go [] = LazyRList (return Nothing)
    go (x:xs) = LazyRList $ do
      factMay <- liftSTM $ readTVar x
      case factMay of
        Just fact
          | if inclusive
            then s `intersects` factTSpan fact
            else _
          -> return $ Just (fact, go xs)
        _ -> unLazyRList (go xs)

    -- WithOUT check if after t
{-
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

liftSTM :: STM a -> Reaction a
liftSTM go = Reaction $ \_ -> do
  a <- go
  return ([], [], Left a)

untilJust :: STM (Maybe a) -> STM a
untilJust go = do
  aMay <- go
  case aMay of
    Nothing -> retry
    Just a -> return a

-}