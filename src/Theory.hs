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

module Theory where

  import qualified Control.Monad as M
  import Control.Applicative
  import Data.Kind
  import Data.List (find, foldl')
  import Data.Maybe (fromMaybe, isNothing, listToMaybe, mapMaybe, maybeToList)
  import qualified Data.Set as S
  import Safe
  import Unsafe.Coerce

  import Time
  -- import KnowledgeBase.Timeline (FactSpan (..))
  import TimeSpan

  import Debug.Trace


  type DerivationTraceEl a = String
  type DerivationTrace a = [DerivationTraceEl a]
  appendDerTrace :: DerivationTrace a -> DerivationTraceEl a -> DerivationTrace a
  appendDerTrace = flip (:)

  data EventFact a
    = FactNoOcc (DerivationTrace a) SpanExc
    | FactMayOcc (DerivationTrace a) Time (MaybeOcc a)

  factTSpan :: EventFact a -> DerivationSpan
  factTSpan (FactNoOcc _ tspan) = DS_SpanExc tspan
  factTSpan (FactMayOcc _ t _) = DS_Point t

  factTrace :: EventFact a -> DerivationTrace a
  factTrace (FactNoOcc tr _) = tr
  factTrace (FactMayOcc tr _ _) = tr

-- We have some set of `EIx`s, 𝔼, and a definition for each: either a source
-- event or derived event and we want to calculate all facts about the derived
-- events from the source events.

  data InputEl = forall a . InputEl (EIx a) (Either [EventFact a] (EventM a))
  type Inputs = [InputEl]

  type MaybeOcc a = Maybe a

  newtype EIx (a :: Type) = EIx Int     -- Index of an event
    deriving newtype (Eq, Ord, Show)

  data SomeEIx = forall a . SomeEIx (EIx a)

  instance Eq SomeEIx where (SomeEIx (EIx a)) == (SomeEIx (EIx b)) = a == b
  instance Ord SomeEIx where compare (SomeEIx (EIx a)) (SomeEIx (EIx b)) = compare a b
  instance Show SomeEIx where show (SomeEIx eix) = show eix

-- Derived events are expressed with the EventM monad:

  data EventM a
    = Pure a
    | NoOcc
    | forall b . GetE  (EIx b) (MaybeOcc b -> EventM a)
    | forall b . PrevE (EIx b) (Maybe  b -> EventM a)

  deriving instance Functor EventM

  instance Applicative EventM where
    (<*>) = M.ap
    pure = return

  instance Monad EventM where
    return = Pure
    fa >>= fmb = case fa of
      Pure a -> fmb a
      NoOcc -> NoOcc
      GetE  eixb mayOccToCont  -> GetE  eixb ((>>= fmb) . mayOccToCont)
      PrevE eixb mayPrevToCont -> PrevE eixb ((>>= fmb) . mayPrevToCont)

  getE :: EIx a -> EventM (MaybeOcc a)
  getE eix = GetE eix Pure

  prevE :: EIx a -> EventM (Maybe a)
  prevE eix = PrevE eix Pure

-- and a useful helper: TODO or we can just use MonadFail and a mono local bind

  requireE :: EIx a -> EventM a
  requireE eix = do
    mayE <- getE eix
    case mayE of
      Nothing -> NoOcc
      Just e -> return e

-- Give some `inputs :: Inputs`, we have this denotation for an event/EventM:

  -- lookupE :: Time -> EIx a -> MaybeOcc a
  -- lookupE t eix = case inputs eix of
  --   Left lookupSourceE -> lookupSourceE t
  --   Right eventM -> deriveE t eventM

  -- deriveE :: forall a . Inputs -> Time -> EventM a -> MaybeOcc a
  -- deriveE t eventM = deriveEgo False eventM
  --
  -- deriveEgo :: Time -> Bool -> EventM a -> MaybeOcc a
  -- deriveEgo t False (Pure _) = Nothing
  -- deriveEgo t True  (Pure a) = Just a
  -- deriveEgo t _   NoOcc  = Nothing
  -- deriveEgo t seenOcc (GetE eixB cont) = case lookupE inputs t eixB of
  --   Nothing -> deriveEgo t seenOcc (cont Nothing)
  --   Just b  -> deriveEgo t True  (cont (Just b))
  -- deriveEgo t seenOcc (PrevE eixB cont)
  --   = if ∃ t'  .  t' < t
  --        ∧  isJust (lookupE t' exiB)
  --        ∧  (∀ t' < t'' < t  .  lookupE t'' exiB == Nothing)
  --     then deriveEgo t (cont (lookupE t' exiB))
  --     else Nothing

  newtype MaybeKnown a = MaybeKnown { maybeKnownToMaybe :: Maybe a }
    deriving newtype (Eq, Ord, Show, Read, Functor, Applicative, Monad)
  pattern Known :: a -> MaybeKnown a
  pattern Known a = MaybeKnown (Just a)
  pattern Unknown :: MaybeKnown a
  pattern Unknown = MaybeKnown Nothing
  {-# COMPLETE Known, Unknown #-}

  lookupEKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
  lookupEKB t eix (KnowledgeBase facts _) = lookupE t eix facts

  lookupE :: Time -> EIx a -> [SomeEventFact] -> MaybeKnown (MaybeOcc a)
  lookupE t eix facts = fmap
    (\case
      FactNoOcc _ _ -> Nothing
      FactMayOcc _ _ occMay -> occMay
    )
    (lookupEFact t eix facts)

  lookupETrace :: Time -> EIx a -> [SomeEventFact] -> MaybeKnown (DerivationTrace a)
  lookupETrace t eix facts = factTrace <$> lookupEFact t eix facts

  lookupEFact :: Time -> EIx a -> [SomeEventFact] -> MaybeKnown (EventFact a)
  lookupEFact t eix facts = MaybeKnown $ listToMaybe $
    filter ((`intersects` t) . factTSpan) (factsE' eix facts)

-- We store a knowledge base:

  data SomeEventFact = forall a . SomeEventFact (EIx a) (EventFact a)
  data SomeDerivation = forall a . SomeDerivation (EIx a) (Derivation a)

  data KnowledgeBase = KnowledgeBase [SomeEventFact] [SomeDerivation]

  factsE :: EIx a -> KnowledgeBase -> [EventFact a]
  factsE eix (KnowledgeBase es _)
    = factsE' eix es

  factsE' :: EIx a -> [SomeEventFact] -> [EventFact a]
  factsE' (EIx eix) es
    = [ unsafeCoerce fact
      | SomeEventFact (EIx eix') fact <- es
      , eix == eix'
      ]

-- A derivation is a partial evaluation of the `deriveE` function, universally
-- quantified over a range of time.

  startDerivationForAllTime :: EventM a -> Derivation a
  startDerivationForAllTime em = Derivation [] (DS_SpanExc allT) [] False em

  -- eix :: Eix a  is implicit
  data Derivation a
    -- When `derPrevTspan /= []` we solve in strictly chronological order.
    --
    -- ∀ t ∈ ttspan   (t <= min_{p ∈ derPrevDeps} {firstOccTime(p, ttspan)}   when derPrevDeps /= [])
    --     . lookup t eix = deriveEgo t False contDerivation
    = Derivation
      { derTrace :: DerivationTrace a
      , derTtspan :: DerivationSpan
      -- ^ Time span/point of jurisdiction.
      , derPrevDeps :: [SomeEIx]
      -- ^ dependencies via PrevE
      , derSeenOcc :: Bool
      -- ^ Has this derivation observed (and hence may produce) an event.
      -- Must be False if derTtspan is a DS_SpanExc (the reverse implication does NOT hold).
      , derContDerivation :: EventM a
      }

    -- ∀ t ∈ tspan (t > firstOccTime(dep, tspan))
    --     . lookup t eix = deriveEgo t False contDerivation
    | forall b . DeriveAfterFirstOcc
      { derTrace :: DerivationTrace a
      , derAfterTspan   :: SpanExc
      , derAfterDep   :: EIx b
      , derAfterContDerivation :: EventM a
      }

    -- This is used after advancing (with a NoOcc fact span) up to (excluding) a
    -- clearance time. At this point we must decide if the derivation has
    -- further jurisdiction. We proceed iff none of the immediate PrevE deps are
    -- occurring at the clearance time.
    --
    -- ∀ t ∈ tspan (∀ d ∈ PrevDeps . lookup (spanExcJustBefore tspan) d == Nothing)
    --     . [[ Derivation (DS_SpanExc tspan) prevDeps False contDerivation ]]
    | AfterClearanceTime
      { derTrace :: DerivationTrace a
      , derClearanceTspan    :: SpanExc
      -- ^ Must not be open on the left (spanExcJustBefore tspan /= Nothing)
      -- this follows from the usage where the lower bound is a clearance time
      -- which cannot be -Inf
      , derClearancePrevDeps :: [SomeEIx]
      , derClearanceContDerivation :: EventM a
      }

  data DerivationSpan
    -- | DS_Point x ⟹ t < x
    = DS_Point Time
    -- | DS_SpanExc tspan ⟹ t ∈ tspan
    | DS_SpanExc SpanExc
    deriving (Show)

    -- -- | DS_SpanExc tspan ⟹ t ∈ tspan
    -- | DS_SpanExcInc SpanExcInc

    -- -- | DS_SpanExcIncFirstOcc lo  ⟹ t ∈ tspan
    -- | forall a . DS_SpanExcIncFirstOcc SpanExc (EIx a)

-- Now a natural fist attempt at a solution is obvious: start with an initial
-- knowledge base and continue evaluating derivations until all terminate or
-- deadlock:

  solution1 :: Inputs -> KnowledgeBase
  solution1 inputs = iterateUntilChange initialKb
    where
    initialFacts = concat
      [ SomeEventFact eix <$> eventFacts
      | InputEl eix (Left eventFacts) <- inputs
      ]
    initialDerivations =
      [ SomeDerivation eix (startDerivationForAllTime eventM)
      | InputEl eix (Right eventM) <- inputs
      ]
    initialKb = KnowledgeBase initialFacts initialDerivations

    iterateUntilChange :: KnowledgeBase -> KnowledgeBase
    iterateUntilChange kb = let (kb', hasChanged) = stepDerivations kb
        in if hasChanged
            then iterateUntilChange kb'
            else kb'

    -- Tries to step all derivations once.
    stepDerivations
      :: KnowledgeBase
      -- ^ Current knowledge base.
      -> (KnowledgeBase, Bool)
      -- ^ (New knowledge base, True is the new knowledge base is different from the old).
    stepDerivations (KnowledgeBase facts derivations)
      = (KnowledgeBase kb'facts kb'derivations, anyChanged)
      where
      (kb'facts, kb'derivations, anyChanged) = foldl'
        (\(facts', derivations', changed)
          someDerivation@(SomeDerivation eix derivation)
          -> case stepDerivation eix derivations facts' derivation of
          Nothing ->
            ( facts'
            , someDerivation:derivations'
            , changed
            )
          Just (newFacts, newDerivations) ->
            ( (SomeEventFact eix <$> newFacts) ++ facts'
            , (SomeDerivation eix <$> newDerivations) ++ derivations'
            , True
            )
        )
        (facts, [], False)
        derivations

    -- This is the important part that should correspond to the `deriveE`
    -- denotation.
    stepDerivation
      :: EIx a
      -- ^ Event index that the derivation corresponds to.
      -> [SomeDerivation]
      -- ^ Current derivations. Used to detect PrevE deadlock.
      -> [SomeEventFact]
      -- ^ Current facts. Used to query for existing facts
      -> Derivation a
      -- ^ Derivation to step
      -> Maybe ([EventFact a], [Derivation a])
      -- ^ Nothing if no progress. Else Just the new facts and new derivations.
    stepDerivation eix allDerivations facts derivation = trace derivationDbg $ case derivation of
      Derivation dtrace ttspan prevDeps seenOcc contDerivation -> case contDerivation of
        Pure a -> if null prevDeps
          then Just $ case (seenOcc, ttspan) of
              (True, DS_Point t) -> let
                dtrace' = appendDerTrace dtrace $
                  ""
                in ([FactMayOcc dtrace' t (Just a)], [])
              -- TODO looks like an invariant that `seenOcc -> ttspan is a point in time (i.e. not a span)`
              (True, DS_SpanExc _) -> error "stepDerivation: encountered non-instantaneous event occurrence."
              (False, DS_Point t) -> ([FactMayOcc t Nothing], [])
              (False, DS_SpanExc tspanSpan) -> ([FactNoOcc tspanSpan], [])
          else stepCompleteWithPrevDeps (Just a)
        NoOcc ->  if null prevDeps
          then Just $ case ttspan of
              DS_Point t      -> ([FactMayOcc t Nothing], [])
              DS_SpanExc tspanSpan -> ([FactNoOcc tspanSpan], [])
          else stepCompleteWithPrevDeps Nothing
        GetE eixb mayOccToCont -> let
          factsBAndUnknownsMay = if null prevDeps
            then Just (spanLookupEFacts ttspan eixb facts)
            -- chronological version of the above with PrevE deps.
            -- TODO this and the above "then" and also the PrevE cases
            -- have very similar code (split on other facts). Try to DRY
            -- it.
            else case find ((ttspan `contains`) . factTSpan) (fst (spanLookupEFacts ttspan eixb facts)) of
              Nothing -> Nothing
              Just fact -> Just ([fact], ttspan `difference` factTSpan fact)
         in case factsBAndUnknownsMay of
            Nothing -> Nothing
            Just ([], _) -> Nothing
            Just (factsB, unknowns) -> Just $ (
                -- For knowns, split and try to progress the derivation.
                mconcat
                  [ case factB of
                    FactNoOcc _ subTspan -> let
                      newCont = mayOccToCont Nothing
                      newDer  = Derivation (DS_SpanExc subTspan) prevDeps seenOcc newCont
                      in fromMaybe
                        ([], [newDer])
                        -- ^ Couldn't progress further: no new facts, but we've progressed the derivation up to newDer.
                        (stepDerivation eix allDerivations facts newDer)
                        -- ^ Try to progress further.
                    FactMayOcc _ t maybeOccB -> case maybeOccB of
                      -- This is simmilar to above
                      Nothing -> let
                        newCont = mayOccToCont Nothing
                        newDer  = Derivation (DS_Point t) prevDeps seenOcc newCont
                        in fromMaybe
                          ([], [newDer])
                          (stepDerivation eix allDerivations facts newDer)
                      Just b -> let
                        newCont = mayOccToCont (Just b)
                        newDer  = Derivation (DS_Point t) prevDeps True newCont
                        in fromMaybe
                          ([], [newDer])
                          (stepDerivation eix allDerivations facts newDer)
                  | factB <- factsB
                  ]
                <>
                -- For unknowns, simply split the derivation into the
                -- unknown subspans.
                ([], [Derivation subTspan prevDeps seenOcc contDerivation | subTspan <- unknowns])
                )

        PrevE eixB mayPrevToCont -> case ttspan of
          -- For reference:
          --   deriveEgo t seenOcc (PrevE eixB cont)
          --   = if ∃ t'  .  t' < t
          --        ∧  isJust (lookupE t' exiB)
          --        ∧  (∀ t' < t'' < t  .  lookupE t'' exiB == Nothing)
          --     then deriveEgo t (cont (lookupE t' exiB))
          --     else Nothing
          DS_Point t -> case lookupPrevE t eixB facts of
            Unknown -> Nothing
            Known prevBMay -> Just $ let
              newCont = mayPrevToCont prevBMay
              newDer  = Derivation ttspan (SomeEIx eixB : prevDeps) seenOcc newCont
              in fromMaybe
                ([], [newDer])
                (stepDerivation eix allDerivations facts newDer)

          -- !! The Plan
          -- !! Try and split on facts about eixB.
          DS_SpanExc tspan -> let
            -- | Nothing means tried chronoloical order, but found no fact.
            factsAndUnknownsMay = if null prevDeps
              then Just (spanLookupPrevE ttspan eixB facts)
              -- chronological version of the above with PrevE deps.
              else case find ((tspan `contains`) . fst) (fst (spanLookupPrevE ttspan eixB facts)) of
                Nothing -> Nothing
                Just knownSpanAndFact -> Just ([knownSpanAndFact], ttspan `difference` fst knownSpanAndFact)

            -- !! If deadlock is detected, proceed by splitting into (1)
            -- !! events after the first eixB event in tspan and (2)
            -- !! chronologically solving before that event.
            checkDeadlock = let
              tspanLo = spanExcJustBefore tspan
              prevValMayIfKnown = case tspanLo of
                Nothing -> Known Nothing -- Known: there is no previous value.
                Just tLo -> lookupCurrE tLo eixB facts
              in case prevValMayIfKnown of
                Unknown -> Nothing
                Known prevValMay -> if deadlockedVia tspanLo eix eixB allDerivations
                  then Just
                    ( []
                    , [ Derivation
                          ttspan
                          (SomeEIx eixB : prevDeps)
                          seenOcc
                          (mayPrevToCont prevValMay)
                      , DeriveAfterFirstOcc
                          tspan
                          eixB
                          contDerivation
                      ]
                    )
                  else Nothing
            in case factsAndUnknownsMay of
              -- TODO I think we don't necessarily need to detect deadlock, we
              -- can always just assume there might be deadlock and derive
              -- chronologically. We'd need to argue that that will not delay
              -- the production of facts, but that seems intuitively true: with
              -- a PrevE dependency, we must solve chronologically (at least
              -- piecewise after known events occs).

              -- !! If there are no such facts, try to detect deadlock via
              -- !! eixB. This means that eix is reachable (transitively) via
              -- !! the PrevE dependencies of derivations coinciding with the
              -- !! start of tspan.
              Nothing -> checkDeadlock
              Just ([], _) -> checkDeadlock

              -- !! Otherwise we can progress by splitting
              Just (knownSpansAndValueMays, unknownSpans) -> Just $ (
                -- For knowns, split and try to progress the derivation.
                mconcat
                  [ let
                    newCont = mayPrevToCont prevEMay
                    newDer  = Derivation ttspan' prevDeps seenOcc newCont
                    in fromMaybe
                      ([], [newDer])
                      -- ^ Couldn't progress further: no new facts, but we've progressed the derivation up to newDer.
                      (stepDerivation eix allDerivations facts newDer)
                      -- ^ Try to progress further.
                  | (ttspan', prevEMay) <- knownSpansAndValueMays
                  ]
                <>
                -- For unknowns, simply split the derivation into the
                -- unknown subspans.
                ([], [Derivation subTspan prevDeps seenOcc contDerivation | subTspan <- unknownSpans])
                )

        where
        -- This is called when a derivation is complete (Pure _ or NoOcc) and
        -- there are some PrevE dependencies.
        --
        -- If the ttspan is a point time, then this is easy! Pure x means event
        -- occurrence with x **iff an event is seen**. NoOcc means NoOcc.
        --
        -- If the ttspan is a span, things get more tricky. At this point we
        -- need to find a "clearance time". This is some time span at the start
        -- of ttspan where whe know none of the PrevE events are occurring
        -- (within the time jurisdiction of this Derivation). We do this by
        -- finding the transitive closure of PrevE dependencies. For each dep we
        -- have either facts indicating for how long no event is occuring, or
        -- complete derivations. The clearance time is just the minimum end time
        -- of the deps' NoOcc spans (from facts) or Derivation spans (from
        -- derivations taking the tspan directly and ignoring it's PrevE events
        -- possibly cutting its jurisdiction off early). I have a proof for this
        -- that I should document here.
        stepCompleteWithPrevDeps occMay = case ttspan of
          DS_Point t
            | seenOcc   -> Just ([FactMayOcc t occMay ], [])
            | otherwise -> Just ([FactMayOcc t Nothing], [])
          DS_SpanExc tspan -> let
            tLoMay = spanExcJustBefore tspan
            -- Clearance time iff after the start of tspan. Note that the
            -- clearance time must be in tspan or at the time just after tspan.
            -- This is a natural consequence of the fact that we observer the
            -- current Derivation as part of the calculation of clearance time.
            ctMay = clearanceTime (SomeEIx eix) tLoMay
            in case ctMay of
              Nothing -> Nothing
              Just ct -> Just
                ( [FactNoOcc (spanExc tLoMay ct)]
                -- If ct is not Inf (i.e. Nothing) and is within the current
                -- jurisdiction (i.e. tspan), then we need to cover the
                -- clearance time at and after ct.
                , case ct of
                    Just ctPoint | tspan `contains` ctPoint
                      -> [ Derivation _ (DS_Point ctPoint) prevDeps seenOcc contDerivation
                         , AfterClearanceTime
                            (spanExc ct (spanExcJustAfter tspan))
                            prevDeps
                            contDerivation
                         ]
                    _ -> []


                -- [ Derivation (DS_Point ctPoint) prevDeps seenOcc contDerivation
                --   | Just ctPoint <- [ct]
                --   , tspan `contains` ctPoint
                --   ] ++
                --   -- If ct is not the end the tspan, then we need to cover the
                --   -- rest of the tspan strictly after ct.
                --   [ _coverAfterCt
                --   | _
                --   ]
                )
                -- !!!!!!!!!!!!!!!!!! I need to make sure that the full jurisdiction is covered. I wonder if I need another Derivation constructor !!!!!!!!!!!!!!!!!!!!
                -- We need a derivations that says "given that none of the immediate PrevE deps are occuring at time `ct`, continue the chonological derivation for span (ct, spanExcJustAfter tspan)"

        clearanceTime
          :: SomeEIx      -- ^ Event in question
          -> Maybe Time   -- ^ Start time of clearance ((exclusive) start of the span of NoOcc ). Nothing means -Inf.
          -> Maybe (Maybe Time)
                          -- ^ Clearance time if greater than the input time ((exclusive) end of the span of NoOcc). Just Nothing means Inf.
        clearanceTime ix' tLo = do
          -- Get the initial clearance
          (neighbors, ixClearanceTime) <- neighborsAndClearance ix'
          go neighbors (S.singleton ix') ixClearanceTime
          where
          go
            :: [SomeEIx] -- ^ stack of events to visit
            -> S.Set SomeEIx -- ^ visited events
            -> Maybe Time -- ^ clearance time so far (if any).
            -> Maybe (Maybe Time) -- ^ clearance time if greater than input time.
          go [] _ clearance = Just clearance
          go (ix:ixs) visited clearance
            | ix `S.member` visited = go ixs visited clearance
            | otherwise = do
                (neighbors, ixClearanceTime) <- neighborsAndClearance ix
                go (neighbors++ixs) (S.insert ix visited) (minClearance ixClearanceTime clearance)

          -- | For clearance time, Nothing means Inf so account for that here.
          minClearance :: Maybe Time -> Maybe Time -> Maybe Time
          minClearance Nothing a = a
          minClearance a Nothing = a
          minClearance (Just a) (Just b) = Just (min a b)

          -- | Get the neighbors (PrevE deps) and clearance time (ignoring
          -- neighbors) of a single event.
          neighborsAndClearance
            :: SomeEIx
            -> Maybe ([SomeEIx], Maybe Time)
          neighborsAndClearance ix
            = (([],) <$> neighborsAndClearanceFacts ix) -- No PrevE deps if a fact.
            <|> neighborsAndClearanceDerivation ix

          -- | Get the neighbors (PrevE deps) and clearance time (ignoring
          -- neighbors) of a single event. Only considers known Facts.
          neighborsAndClearanceFacts
            :: SomeEIx
            -> Maybe (Maybe Time)
          neighborsAndClearanceFacts ix@(SomeEIx ix_) = findClearanceAfter tLo
            where
            findClearanceAfter :: Maybe Time -> Maybe (Maybe Time)
            findClearanceAfter t = listToMaybe
              [ case spanExcJustAfter tspan of
                  Nothing -> Nothing
                  Just nextT -> findClearanceAt nextT
              | SomeEventFact ix'' (FactNoOcc _ tspan) <- facts
              , ix == SomeEIx ix''
              , case t of
                  Nothing -> spanExcJustBefore tspan == Nothing
                  Just tt -> tspan `contains` tt
              ]

            findClearanceAt :: Time -> Maybe Time
            findClearanceAt t = case lookupE t ix_ facts of
              Unknown -> Just t -- Point gap in knowledge. Stop clearance traversal.
              Known (Just _) -> Just t -- Event is occurring. Stop clearance traversal.
              -- No event is occuring at time t. Keep traversing.
              Known Nothing -> case findClearanceAfter (Just t) of
                Nothing -> Just t
                Just clearance -> clearance

          -- | Get the neighbors (PrevE deps) and clearance time (ignoring
          -- neighbors) of a single event. Only considers active Derivations.
          neighborsAndClearanceDerivation
            :: SomeEIx
            -> Maybe ([SomeEIx], Maybe Time)
          neighborsAndClearanceDerivation ix = listToMaybe
            [ (neighbors, spanExcJustAfter tspan)
            | SomeDerivation
                ix''
                (Derivation
                  _
                  (DS_SpanExc tspan)
                  neighbors
                  _
                  cont
                )
                <- allDerivations
            , ix == SomeEIx ix'' -- look up the correct eix
            , spanExcJustBefore tspan == tLo -- starts at tLo
            -- derivation is complete
            , case cont of
                Pure _ -> True
                NoOcc  -> True
                _ -> False
            ]

      DeriveAfterFirstOcc dtrace tspan eixB cont -> case searchForFirstEventOcc tspan eixB facts of
        -- We know the time of the first occurrence, so we can convert
        -- to a concrete time span again.
        FirstOccIsAt firstOccTime -> let
          -- Safe to use mono-bind here as firstOccTime ∈ tspan
          Just concreteTimeSpan = tspan `intersect` RightSpaceExc firstOccTime
          newDer = Derivation
            (DS_SpanExc concreteTimeSpan)
            []
            -- ^ NOTE [DeriveAfterFirstOcc and PrevE deps] There are
            -- no PrevE events by denotation of DeriveAfterFirstOcc
            False
            cont
          in Just ([], [newDer])

        -- We know the right of clearanceTime (exclusive) is definitely
        -- after the first event.
        FirstOccIsAtOrBefore clearanceTime -> let
          -- NOTE we keep seenOcc as False. This follows from the
          -- definition of DeriveAfterFirstOcc. Intuitivelly, we are
          -- only dealing with *when* the first event is, not handling
          -- the event itself. The event (if one exists) will be
          -- handled by the new derivations.
          seenOcc = False

          newDers =
            [ let Just tspanBefore = tspan `intersect` LeftSpaceExc clearanceTime
               in DeriveAfterFirstOcc tspanBefore eixB cont

            , Derivation (DS_Point clearanceTime) [] seenOcc cont
            -- See NOTE [DeriveAfterFirstOcc and PrevE deps]

            , let Just tspanAfter = tspan `intersect` RightSpaceExc clearanceTime
               in Derivation (DS_SpanExc tspanAfter) [] seenOcc cont
            -- See NOTE [DeriveAfterFirstOcc and PrevE deps]
            ]
          in Just ([], newDers)

        -- There is no first occ, so this derivation covers no time, so
        -- we stop.
        NoOccInSpan -> Just ([], [])

        -- We don't know any more info about the first occurrence so we
        -- cant make any more progress.
        Other -> Nothing

      AfterClearanceTime dtrace tspan prevDeps contDer -> case prevDepsAreNotOccurringMay of
        -- Only when we know that no prevDeps are occuring can we continue.
        Known True -> Just ([], [Derivation (DS_SpanExc tspan) prevDeps False contDer])
        Known False -> Nothing
        Unknown -> Nothing
        where
        prevDepsAreNotOccurringMay :: MaybeKnown Bool
        prevDepsAreNotOccurringMay = not . and <$> (sequence
          [ isNothing <$> lookupE ct dep facts
          | SomeEIx dep <- prevDeps
          ])

        ct :: Time
        Just ct = spanExcJustBefore tspan

      where
      derivationDbg = (show eix) ++ " " ++ case derivation of
        Derivation _ ttspan prevDeps seenOcc _
          -> "Derivation ("
          ++ show ttspan ++ ") "
          ++ show prevDeps ++ " "
          ++ show seenOcc
        DeriveAfterFirstOcc _ tspan dep _
          -> "DeriveAfterFirstOcc ("
          ++ show tspan ++ ") ("
          ++ show dep ++ ")"
        AfterClearanceTime _ ct deps _
          -> "AfterClearanceTime "
          ++ show ct ++ " "
          ++ show deps

  -- | Try to detect deadlock via a cycle of PrevE dependencies including eixA
  -- and eixB just after the given time.
  --
  -- True means deadlock detected: a cycle of PrevE events was found.
  --
  -- False means deadlock may or may not exist: no cycle of PrevE events was
  -- found.
  deadlockedVia
    :: Maybe Time
    -- ^ Just after time to sample dependencies (Nothing means negative
    -- infinity)
    -> EIx a
    -- ^ eixA must depend on eixB (possible transitively)
    -> EIx b
    -- ^ eixB
    -> [SomeDerivation]
    -- ^ Known derivations (used to infer dependencies)
    -> Bool
  deadlockedVia t (EIx eixA) (EIx eixB) ders = go [eixB] S.empty
    where
    -- | DFS to see if eixA is reachable from the starting set
    go [] _ = False
    go (x:xs) visited
      | x == eixA   = True
      | x `S.member` visited
              = go xs visited
      | otherwise   = go (deps x ++ xs) (S.insert x visited)

    deps x = concat -- We actually expect at most one element.
      [ [dep | SomeEIx (EIx dep) <- prevDeps]
      | SomeDerivation (EIx x') (Derivation _ (DS_SpanExc tspan) prevDeps _ _) <- ders
      , x == x'
      -- NOTE we're not looking for "tspan contains t+" as we can only
      -- infer deadlock when tspan starts exactly on t (otherwise we dont
      -- actually know when the derivation's jurisdiciton ends due to its
      -- PrevE deps).
      , spanExcJustBefore tspan == t
      ]

  -- | Result of searching for the first event occurence of a specific event
  -- and time span.
  data FirstEventOcc
    -- | Enough information is known such that we can be sure this is the
    -- first occurrence.
    = FirstOccIsAt Time
    -- | Enough information is known such that we can be sure the first
    -- occurrence is at or before this time. This time will be the first
    -- *known* event occurence, but there will be some unknown point or span
    -- of time before this event that may contain the true first event.
    | FirstOccIsAtOrBefore Time
    -- | We have full information and know that no event is occurring in the
    -- searched span.
    | NoOccInSpan
    -- | Some facts are missing such that we cant say anything about the
    -- first occurence.
    | Other

  searchForFirstEventOcc
    :: SpanExc
    -- ^ Time span to lookup
    -> EIx a
    -- ^ Event to lookup
    -> [SomeEventFact]
    -- ^ All known facts.
    -> FirstEventOcc
  searchForFirstEventOcc tspan eix allFacts = let
    (facts, unknownDSpans) = spanLookupEFacts (DS_SpanExc tspan) eix allFacts
    firstKnownOccTMay = minimumMay [ t | FactMayOcc _ t (Just _)  <- facts]
    in case firstKnownOccTMay of
      -- No known first occurrence and total knowledge means no occurrence.
      Nothing -> if null unknownDSpans then NoOccInSpan else Other
      Just firstKnownOccT -> let
        -- We know firstKnownOccT ∈ tspan
        Just spanBeforeFirstKnownOccT = tspan `intersect` RightSpaceExc firstKnownOccT
        -- First known occ is the true first occ if we have total
        -- knowledge before that time.
        isTrueFirstOcc = not $ any (intersects spanBeforeFirstKnownOccT) unknownDSpans
        in if isTrueFirstOcc
          then FirstOccIsAt     firstKnownOccT
          else FirstOccIsAtOrBefore firstKnownOccT


  -- | Directly look up the previous event occurrence (strictly before the given time).
  lookupPrevE
    :: Time
    -- ^ Time t
    -> EIx a
    -- ^ Event to lookup.
    -> [SomeEventFact]
    -- ^ Known facts.
    -> MaybeKnown (Maybe a)
    -- ^ Nothing if unknown
    -- Just Nothing if no event occurs before t.
    -- Just (Just a) the value of the latest event occurring strictly before t.
  lookupPrevE t eix allFacts = let
    noOccSpans = mapMaybe
        (\case
          FactMayOcc _ _ _ -> Nothing
          FactNoOcc _ tspan -> Just tspan
        )
        (factsE' eix allFacts)
    -- We must find a FactMayOcc just before or containing t.
    tspanMay = find
        (\tspan -> tspan `contains` t || Just t == spanExcJustAfter tspan)
        noOccSpans
    in case tspanMay of
      Nothing -> Unknown
      Just tspan -> case spanExcJustBefore tspan of
        Nothing -> Known Nothing
        Just t' -> lookupCurrE t' eix allFacts

  -- | Directly look up the current (i.e. latest) event occurrence (equal or before the given time).
  lookupCurrE
    :: Time
    -- ^ Time t
    -> EIx a
    -- ^ Event to lookup.
    -> [SomeEventFact]
    -- ^ Known facts.
    -> MaybeKnown (Maybe a)
    -- ^ Nothing if unknown
    -- Just Nothing if no event occurs before t.
    -- Just (Just a) the value of the latest occurring at or before t.
  lookupCurrE t eix allFacts = let
    facts = factsE' eix allFacts
    factMay = find (\f -> factTSpan f `contains` t) facts
    in case factMay of
      Nothing -> Unknown
      Just fact -> case fact of
        FactNoOcc _ tspan -> case spanExcJustBefore tspan of
          Nothing -> Known Nothing
          Just t' -> lookupCurrE t' eix allFacts
        FactMayOcc _ _ Nothing -> lookupPrevE t eix allFacts
        FactMayOcc _ _ (Just a) -> Known (Just a)


  -- | Directly lookup the previous value for an event over a span of time.
  spanLookupPrevE
    :: DerivationSpan
    -- ^ Time or span to lookup
    -> EIx a
    -- ^ Event to lookup
    -> [SomeEventFact]
    -- ^ All known facts.
    -> ([(DerivationSpan, Maybe a)], [DerivationSpan])
    -- ^ ( Known values about the given event
    --   , unknown times and time spans )
    --   The union of these times and time spans should exactly
    --   equal the input time/time span.
  spanLookupPrevE tspan eix allFacts = let
    facts = prevEFacts eix allFacts
    knownFacts =
        [ (ttspan', aMay)
        | (factTspan, aMay) <- facts
        , Just ttspan' <- [factTspan `intersect` tspan]
        ]
    knownTSpans = fst <$> knownFacts
    unknownTSpans = tspan `difference` knownTSpans
    in (knownFacts, unknownTSpans)


  -- | Get all known PervE spans for an event
  prevEFacts
    :: forall a
    .  EIx a
    -- ^ Event to lookup
    -> [SomeEventFact]
    -- ^ All known facts.
    -> [(DerivationSpan, Maybe a)]
    -- ^ All known previous event values (if one exists)
  prevEFacts eix allFacts = concat
    [ case fact of
      FactNoOcc _ tspan -> let
        mayPrevEMay :: MaybeKnown (Maybe a)
        mayPrevEMay = case spanExcJustBefore tspan of
          -- Span starts at -∞ so that's a known Nothing previous event
          Nothing -> Known Nothing
          -- Span starts at a time prevT
          Just prevT -> lookupCurrE prevT eix allFacts
        in case mayPrevEMay of
            Unknown -> []
            Known prevEMay -> (DS_SpanExc tspan, prevEMay) : [(DS_Point nextT, prevEMay) | Just nextT <- [spanExcJustAfter tspan]]
      FactMayOcc _ _ _ -> [] -- Point knowledge is handled by the above case
    | fact <- factsE' eix allFacts
    ]

  -- | Directly look up all known facts for a given event and time or time
  -- span.
  spanLookupEFacts
    :: DerivationSpan
    -- ^ Time or span to lookup
    -> EIx a
    -- ^ Event to lookup
    -> [SomeEventFact]
    -- ^ All known facts.
    -> ([EventFact a], [DerivationSpan])
    -- ^ ( Facts about the given event
    --   , unknown times and time spans )
    --   The union of these facts and times and time spans should exactly
    --   equal the input time/time span.
  spanLookupEFacts tspan eix allFacts = let
    facts = factsE' eix allFacts
    knownFacts =
        [ case (fact, ttspan') of
          (FactNoOcc _ _, DS_SpanExc tspan') -> FactNoOcc tspan'
          (FactNoOcc _ _, DS_Point t'   ) -> FactMayOcc t' Nothing
          (FactMayOcc _ _ _   , DS_SpanExc _) -> error "Intersection between SpanExc and Time must be Just Time or Nothing"
          (FactMayOcc _ _ occMay, DS_Point t') -> FactMayOcc t' occMay
        | fact <- facts
        , Just ttspan' <- [factTSpan fact `intersect` tspan]
        ]
    knownTSpans = factTSpan <$> knownFacts
    unknownTSpans = tspan `difference` knownTSpans
    in (knownFacts, unknownTSpans)


{-

## Here is a working example:

  eix1, eix2, eix3 :: EIx Int
  eix1 = EIx 1
  eix2 = EIx 2
  eix3 = EIx 3

  kb :: KnowledgeBase
  kb = solution1
      [ InputEl eix1
        (Left [ FactNoOcc (spanExc Nothing (Just 7))
            , FactMayOcc 7 (Just 9)
            ]
        )
      , InputEl eix2
        (Left [ FactNoOcc (spanExc Nothing (Just 5))
            , FactMayOcc 5 (Just 90)
            , FactMayOcc 7 (Just 80)
            ]
        )
      , InputEl eix3
        (Right $ do
          e1 <- fromMaybe 0 <$> getE eix1
          e2 <- fromMaybe 0 <$> getE eix2
          return (e1+e2+100)
        )
      ]
















-}












{-
{-
# NFRP Implementation and Semantics

NFRP is a networked FRP system. We start by looking only at "Events"

## Background

### Semantics of Total Event

We use a continuous time type `Time`. In practice we use `Int64` representing
nanoseconds.

Consider an `Event a` this represents a stream of events happening at distinct
times. This is "total" in the sense that it is complete knowledge of all event
occurrences for all time. As is typical of FRP systems we have the following
denotation:

  ⟦ Event a ⟧ = [(Time, a)]   -- Where Time values are distinct.

Note that `⟦x⟧` means "denotation of x" and `[x]` is regular haskell syntax
meaning "a list of x". As the time values are distinct, this means that at any
point in time an event is occurring either exactly once or not at all. We can now
answer the question of "is an event occurring at a given time?":
-}
  type MaybeOcc a = Maybe a
{-
  lookupTotalE :: Time -> Event a -> MaybeOcc a
  lookupTotalE = lookup

This is a clear and simple denotation, and is ultimately the mental model users
of the NFRP library will use when writing the logic of their program. When it
comes to implementation of NFRP a richer denotation will be used.

## KnowledgeBase

In practice we only ever have partial knowledge that evolves as the program
runs, receives new inputs, and communicates with other "nodes" over a network.
Hence, when considering implementation, we make use of a `KnowledgeBase`. We
also refer to Events with an event index.
-}
  newtype EIx (a :: Type) = EIx Int     -- Index of an event
    deriving newtype Eq

  data SomeEventFact = forall a . SomeEventFact (EIx a) (EventFact a)

  data KnowledgeBase = KnowledgeBase [SomeEventFact]

  newKnowledgeBase :: KnowledgeBase
  newKnowledgeBase = KnowledgeBase []

  factsE :: EIx a -> KnowledgeBase -> [EventFact a]
  factsE (EIx eix) (KnowledgeBase es)
    = [ unsafeCoerce fact
      | SomeEventFact (EIx eix') fact <- es
      , eix == eix'
      ]
{-
That represents the current knowledge of a set of events (and later also
behaviors). As we receive new facts, we can add them to the `KnowledgeBase`:

  insertFact :: SomeEventFact -> KnowledgeBase -> KnowledgeBase
  insertFact = ...

This isn't as simple as appending facts as we also want to derive knowledge from
existing facts. How exactly we derive all this knowledge is a main source of
complexity when implementing NFRP.

# Semantics of (Partial) Event

Throughout the implementation of NFRP we always think of events as partial i.e.
we only have knowledge of events for explicit periods of time. We make partial
knowledge explicit with the following denotation:

  ⟦ Event a ⟧ = [EventFact a]   -- Where facts' time spans never overlap

  data SpanExc = ...
-}
  data EventFact a
    = NoOcc SpanExc    -- No event is occurring in this time span.
    | Occ Time (Maybe a)   -- A single event may be occurring at this time.
{-
So now not only do we store the event occurrences (`Occ Time a` or in the
old denotation `(Time, a)`), but we also store the spans of time where we know
there are no event occurrences, `NoOcc SpanExc`. All time not covered by
these facts is implicitly "unknown". Now our `lookupE` function changes a bit:
-}
  type MaybeKnown a = Maybe a

  lookupE :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
  lookupE time eix kb = case find (\fact -> toFactSpan fact `contains` time) (factsE eix kb) of
    Just (NoOcc _)  -> Just Nothing
    Just (Occ _ aMay) -> Just aMay
    Nothing       -> Nothing

  isOccurring :: Time -> EIx a -> KnowledgeBase -> Maybe Bool
  isOccurring time eix kb = fmap isJust (lookupE time eix kb)

  toFactSpan :: EventFact a -> FactSpan
  toFactSpan (NoOcc tspan) = FS_Span tspan
  toFactSpan (Occ t _) = FS_Point t
{-
## Source and Derived Events

Now that we have a denotation/representation for events, we can easily construct
events directly like so:

  -- An event that never occurs.
  e1 = Event [NoOcc (spanExc Nothing Nothing)]

  -- An event that occurs at time 10 and unknown at and after time 100.
  e1 = Event
      [ NoOcc (spanExc Nothing (Just 10))
      , Occ 10 "Hi, I'm an event occurrence at time 10"
      , NoOcc (spanExc (Just 10) (Just 100))
      ]

This method of constructing events is how we'll ultimately express the input
events to our program. We'll call these input events "source events". In a large
program, we expect there to only be a small set of input events compared to the
total number of events we want to describe. In the context of a video games, we
may only have a single source event `Event PlayerInputs` from which the entire
game logic will be derived. So we need a way to create "derived events" from
other events. NFRP provides a Monadic interface for this. The *Monadic* part is
a key feature distinguishing NFRP from other FRP libraries. A key advantage to
the monadic style is that it makes "switching" very natural (`switch` is just
`join`).

The `EventM` monad is used to describe a derived event:
-}

  data EventM a
    = forall b . GetE (EIx b) (MaybeOcc b -> EventM a)
    | ReturnOcc a
    | ReturnNoOcc
    -- These are explained in the next section.
    -- | forall b . LatestE   (EIx b) (Maybe b -> EventM a)
    | forall b . PreviousE (EIx b) (Maybe b -> EventM a)

  deriving instance Functor EventM

  -- | Required this event to be occurring in order for the resulting event to
  -- be occur.
  requireE :: EIx a -> EventM a
  requireE eix = GetE eix (maybe ReturnNoOcc ReturnOcc)

  -- | Optionally require this event. In order for the resulting event to
  -- occur, at least 1 of all `getE`ed events must be occurring.
  getE :: EIx a -> EventM (MaybeOcc a)
  getE eix = GetE eix (maybe (ReturnOcc Nothing) (ReturnOcc . Just))

{-
So the event expressed by a `EventM` withe index `eix` has the following
property. Given `getE` dependencies, gDeps, and `requireE` dependencies, rDeps,
and assuming a Time and KnowledgeBase:

  isOccurring eix  <->  any isOccurring gDeps   (null rDeps)
              all isOccurring rDeps   (otherwise)

Note that this implies that if `(null rDeps && null gDeps)` then the `eix` event
NEVER occurs. Also note that since this is monadic, `gDeps` and `rDeps` may
depend on the values of previous dependencies. Here is an example of a game over
event for some imagined 2 player game:

  -- player1DeadE, player2DeadE :: EIx ()

  do
    player1DeadMay <- getE player1DeadE
    player2DeadMay <- getE player2DeadE
    case (player1DeadMay, player2DeadMay) of
      (Just (), Nothing) -> return (Just "Player 2 wins!")
      (Nothing, Just ()) -> return (Just "Player 1 wins!")
      (Just (), Just ()) -> return (Just "It's a tie!")
      (Nothing, Nothing)
        -> error "Impossible! At least one of the getE events must be \
             \occurring (since there are not requireE events)"

This event occurs when one of the players dies, and also handles the case of
both players dieing at the same time. Having to handle the `(Nothing, Nothing)`
is a bit unfortunate, but I can't see much of a way around this.

Here is another example for a multiplayer game with possibly many winners. This
event occurs at the end of the game if player 1 died at exactly the end of the
game.

  -- endOfGameE :: EIx ()

  do
    requireE endOfGameE
    player1DeadMay <- getE player1DeadE
    case player1DeadMay of
      Nothing -> return Nothing
      Just () -> return (Just "Player 1 died at the end of the game")
-}
{-

## Latest / Previous Event value.

Another way at query an event is to consider that latest or previous event
occurrence. That is the latest event occurrence at any given time. This is
partial as such a value doesn't exits until at/after the first event occurrence.
-}

  -- NOTE these have to ensure we have complete knowledge from the
  -- latest/previous occurrence till the target time.

  latestE :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (Maybe a)
  latestE = error "TODO latestE"

  previousE :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (Maybe a)
  previousE = error "TODO previousE"
{-
### State

Before the addition of latestE/previousE, there was no way to access old state.
Indeed, without these functions, events are entirely stateless and can be fully
derived from the current time's source events. latestE/previousE allow us to
look back in time and introduce an evolving state. Here is an example where we
simply count the number of times another event occurs.

  -- otherEvent :: EIx ()

  -- countE :: EIx Int
  -- TODO initially 0
  do
    requireE otherEvent
    currentCount <- previousE countE
    return (Just (currentCount + 1))



## Problematic case

These 2 are actually semantically the same:

  aE = event $ do
    requireE otherEvent
    currentCount <- previousE aE
    return (Just (currentCount + 1))

  bE = event $ do
    _ <- getE otherEvent
    currentCount <- previousE countE
    return (Just (currentCount + 1))

But the `getE` causes a deadlock with a naive implementation. That's because of
the self reference. Imagine we have these source facts:

  otherEventFacts
    = [ NoOcc (spanExc Nothing (Just 10))
      , Occ 10 ()
      ]

We should be able to derive these facts:

  aE facts = bE facts
    = [ NoOcc (spanExc Nothing (Just 10))
      , Occ 10 1
      ]

In case A we'll succeed in deriving this because the EventM short circuits when
seeing otherEvent's NoOcc, and immediatelly gives NoOcc for A from time NegInf
to 10. In B, after seeing the NoOcc of otherEvent, we can't short circuit
because we've used `getE`. Instead we move to the next dependency which is a
self dependency. Deadlock!

It is tempting to try and solve this problem by somehow identifying and managing
self dependencies, but the problem is more general. Consider what happens when I
split bE into multiple events. There are no self references, only indirect self
references:

  aE = event $ do
    _ <- getE otherEvent
    currentCount <- previousE dE
    return (Just (currentCount + 1))

  bE = event $ getE aE
  cE = event $ getE aE

  dE = event $ do
    bMay <- getE bE
    cMay <- getE cE
    return (bMay <|> cMay)

How can we possibly make progress here (i.e. produce facts)?

My *intuition* says that if a set of running EventMs over a common time span
depend on each others' output (i.e. form a transitive closure), then... then
what? Well then we have a deadlock. For spans (not points) of time where we know
that it must start with a NoOcc span (either a subset or equal to the larger
span), we just don't know when the span will end. It ends at the next closest (in time) event occurence



-}

{- APPENDIX -}

  -- TODO

  instance Applicative EventM where
  instance Monad EventM where
-}

  instance Intersect DerivationSpan SpanExc (Maybe DerivationSpan) where intersect = flip intersect
  instance Intersect SpanExc DerivationSpan (Maybe DerivationSpan) where
    intersect t (DS_Point t')     = DS_Point   <$> intersect t t'
    intersect t (DS_SpanExc tspan)  = DS_SpanExc <$> intersect t tspan

  instance Intersect Time DerivationSpan (Maybe Time) where intersect = flip intersect
  instance Intersect DerivationSpan Time (Maybe Time) where
    intersect (DS_Point t)     t' = intersect t t'
    intersect (DS_SpanExc tspan) t  = intersect tspan t

  instance Intersect DerivationSpan DerivationSpan (Maybe DerivationSpan) where
    intersect (DS_Point t)     ds = DS_Point <$> intersect t ds
    intersect (DS_SpanExc tspan) ds = intersect tspan ds

  instance Contains DerivationSpan DerivationSpan where
    contains (DS_Point a) (DS_Point b) = contains a b
    contains (DS_Point a) (DS_SpanExc b) = contains a b
    contains (DS_SpanExc a) (DS_Point b) = contains a b
    contains (DS_SpanExc a) (DS_SpanExc b) = contains a b

  instance Contains SpanExc DerivationSpan where
    contains a (DS_Point b) = contains a b
    contains a (DS_SpanExc b) = contains a b

  instance Contains DerivationSpan Time where
    contains (DS_Point t) t' = contains t t'
    contains (DS_SpanExc tspan) t = contains tspan t

  instance Difference DerivationSpan DerivationSpan [DerivationSpan] where
    difference (DS_Point a) (DS_Point b)
      | a == b = []
      | otherwise = [DS_Point a]
    difference (DS_Point a) (DS_SpanExc b) = fmap DS_Point . maybeToList $ a `difference` b
    difference (DS_SpanExc a) (DS_Point b) = DS_SpanExc <$> a `difference` b
    difference (DS_SpanExc a) (DS_SpanExc b) = concat
      [ l ++ r
      | let (x, y) = a `difference` b
      , let l = case x of
              Nothing -> []
              Just (tspan, t) -> [DS_SpanExc tspan, DS_Point t]
      , let r = case y of
              Nothing -> []
              Just (t, tspan) -> [DS_SpanExc tspan, DS_Point t]
      ]
  instance Difference [DerivationSpan] DerivationSpan [DerivationSpan] where
    difference a b = concatMap (`difference` b) a
  instance Difference DerivationSpan [DerivationSpan] [DerivationSpan] where
    difference a bs = foldl' difference [a] bs