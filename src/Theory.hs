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
  import Data.Hashable
  import Data.Kind
  import Data.List (find, foldl')
  import Data.Maybe (fromMaybe, isNothing, listToMaybe, mapMaybe, maybeToList)
  import qualified Data.Set as S
  import Safe
  import Unsafe.Coerce

  import Time
  import TimeSpan

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
    deriving newtype (Eq, Ord, Show, Hashable)

  data SomeEIx = forall a . SomeEIx (EIx a)

  instance Eq SomeEIx where (SomeEIx (EIx a)) == (SomeEIx (EIx b)) = a == b
  instance Ord SomeEIx where compare (SomeEIx (EIx a)) (SomeEIx (EIx b)) = compare a b
  instance Show SomeEIx where show (SomeEIx eix) = show eix
  instance Hashable SomeEIx where
    hash (SomeEIx a) = hash a
    hashWithSalt i (SomeEIx a) = hashWithSalt i a

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

  lookupEKBTrace :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (DerivationTrace a)
  lookupEKBTrace t eix (KnowledgeBase facts _) = lookupETrace t eix facts

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
    stepDerivation eix allDerivations facts derivation = case derivation of
      Derivation dtrace ttspan prevDeps seenOcc contDerivation -> case contDerivation of
        Pure a -> if null prevDeps
          then Just $ case (seenOcc, ttspan) of
              (True, DS_Point t) -> let
                dtrace' = appendDerTrace dtrace $
                  "Jurisdiction is a point (t=" ++ show t ++ "), we've \
                  \witnessed some GetE event and EventM is \
                  \`Pure a`. This means an event is occurring with value a."
                in ([FactMayOcc dtrace' t (Just a)], [])
              -- TODO looks like an invariant that `seenOcc -> ttspan is a point in time (i.e. not a span)`
              (True, DS_SpanExc _) -> error "stepDerivation: encountered non-instantaneous event occurrence."
              (False, DS_Point t) -> let
                dtrace' = appendDerTrace dtrace $
                  "Jurisdiction is a point (t=" ++ show t ++ "), we've \
                  \NOT witnessed any GetE event and EventM is \
                  \`Pure a` (which is suspect). This means an event is NOT occurring."
                in ([FactMayOcc dtrace' t Nothing], [])
              (False, DS_SpanExc tspanSpan) -> let
                dtrace' = appendDerTrace dtrace $
                  "Jurisdiction is (" ++ show tspanSpan ++ "), we've NOT\
                  \witnessed any GetE event and EventM is \
                  \`Pure a` (which is suspect). This means an event is NOT occurring with ."
                in ([FactNoOcc dtrace' tspanSpan], [])
          else stepCompleteWithPrevDeps (Just a)
        NoOcc ->  if null prevDeps
          then Just $ case ttspan of
              DS_Point t      -> let
                dtrace' = appendDerTrace dtrace $
                  "Jurisdiction is a poiint (" ++ show ttspan ++ "), we've NOT\
                  \witnessed any GetE event and EventM is \
                  \`Pure a` (which is suspect). This means an event is NOT occurring with ."
                in ([FactMayOcc dtrace' t Nothing], [])
              DS_SpanExc tspanSpan -> let
                dtrace' = appendDerTrace dtrace $
                  "EventM says NoOcc for this span."
                in ([FactNoOcc dtrace' tspanSpan], [])
          else stepCompleteWithPrevDeps Nothing
        GetE eixb mayOccToCont -> let
          factsBAndUnknownsMay = if null prevDeps
            then Just (spanLookupEFacts ttspan eixb facts)
            -- chronological version of the above with PrevE deps.
            -- TODO this and the above "then" and also the PrevE cases
            -- have very similar code (split on other facts). Try to DRY
            -- it.

            else case find isChronological (fst (spanLookupEFacts ttspan eixb facts)) of
              Nothing -> Nothing
              Just fact -> Just ([fact], ttspan `difference` factTSpan fact)

          isChronological :: EventFact a -> Bool
          isChronological fact = case ttspan of
            DS_Point _ -> True  -- we use the assumption that fact is in ttspan
            DS_SpanExc tspan -> case factTSpan fact of
              DS_Point _ -> False
              DS_SpanExc tspan' -> spanExcSameLowerBound tspan tspan'

         in case factsBAndUnknownsMay of
            Nothing -> Nothing
            Just ([], _) -> Nothing
            Just (factsB, unknowns) -> Just $ (
                -- For knowns, split and try to progress the derivation.
                mconcat
                  [ case factB of
                    FactNoOcc _ subTspan -> let
                      newCont = mayOccToCont Nothing
                      newDer  = Derivation dtrace (DS_SpanExc subTspan) prevDeps seenOcc newCont
                                  `withDerTrace`
                                  ("Split on GetE dep (" ++ show eixb ++ ") FactNoOcc")
                      in fromMaybe
                        ([], [newDer])
                        -- ^ Couldn't progress further: no new facts, but we've progressed the derivation up to newDer.
                        (stepDerivation eix allDerivations facts newDer)
                        -- ^ Try to progress further.
                    FactMayOcc _ t maybeOccB -> case maybeOccB of
                      -- This is simmilar to above
                      Nothing -> let
                        newCont = mayOccToCont Nothing
                        newDer  = Derivation dtrace (DS_Point t) prevDeps seenOcc newCont
                                  `withDerTrace`
                                  ("Split on GetE dep (" ++ show eixb ++ ") FactMayOcc (No Occ)")
                        in fromMaybe
                          ([], [newDer])
                          (stepDerivation eix allDerivations facts newDer)
                      Just b -> let
                        newCont = mayOccToCont (Just b)
                        newDer  = Derivation dtrace (DS_Point t) prevDeps True newCont
                                  `withDerTrace`
                                  ("Split on GetE dep (" ++ show eixb ++ ") FactMayOcc (With Occ)")
                        in fromMaybe
                          ([], [newDer])
                          (stepDerivation eix allDerivations facts newDer)
                  | factB <- factsB
                  ]
                <>
                -- For unknowns, simply split the derivation into the
                -- unknown subspans.
                ( []
                , [ Derivation dtrace subTspan prevDeps seenOcc contDerivation
                    `withDerTrace`
                    ("Split on GetE dep (" ++ show eixb ++ ") unknown point or span.")
                  | subTspan <- unknowns
                  ]
                )
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
              newDer  = Derivation dtrace ttspan (SomeEIx eixB : prevDeps) seenOcc newCont
                    `withDerTrace`
                    ("Use known PrevE value of dep (" ++ show eixB ++ ")")
              in fromMaybe
                ([], [newDer])
                (stepDerivation eix allDerivations facts newDer)

          -- !! The Plan
          -- !! Try and split on facts about eixB.
          DS_SpanExc tspan -> let
            -- | Nothing means tried chronological order, but found no fact.
            factsAndUnknownsMay = if null prevDeps
              then Just (spanLookupPrevE ttspan eixB facts)
              -- chronological version of the above with PrevE deps.
              else case find ((tspan `contains`) . fst) (fst (spanLookupPrevE ttspan eixB facts)) of
                Nothing -> Nothing
                Just knownSpanAndFact -> Just ([knownSpanAndFact], ttspan `difference` fst knownSpanAndFact)

            -- !! Split into (1) events after the first eixB event in tspan and
            -- !! (2) chronologically solving before that event.
            -- Previously we checked for deadlock and only started solving
            -- chronologically if deadlocked via eixB. This is not necessary, we
            -- can just always solve chronologically. It seems like this would
            -- fail to produce knowable facts that are not chronological, but that
            -- problem is solved by a second derivation with jurisdiction after
            -- the first occurrence of eixB. Since the previous (PrevE) value is
            -- only known for spans of NoOcc after an event occurrence, we know
            -- that chronological before the first occurrence of eixB will be
            -- productive (produce facts as soon as they are knowable).
            tryChonologicalSplit = let
              tspanLo = spanExcJustBefore tspan
              prevValMayIfKnown = case tspanLo of
                Nothing -> Known Nothing -- Known: there is no previous value.
                Just tLo -> lookupCurrE tLo eixB facts
              in case prevValMayIfKnown of
                Unknown -> Nothing
                Known prevValMay -> Just
                    ( []
                    , [ Derivation
                          dtrace
                          ttspan
                          (SomeEIx eixB : prevDeps)
                          seenOcc
                          (mayPrevToCont prevValMay)
                        `withDerTrace`
                          ("Deadlock detected via " ++ show eixB ++ " (at t=" ++ show tspanLo ++ "). Store "
                          ++ show eixB ++ " as a PrevE dep and solve chronologically")
                      , DeriveAfterFirstOcc
                          dtrace
                          tspan
                          eixB
                          contDerivation
                        `withDerTrace`
                          ("Deadlock detected via " ++ show eixB
                          ++ " (at t=" ++ show tspanLo ++ "). Wait for first occ of " ++ show eixB
                          ++ " and solve for the rest of the time span if any.")
                      ]
                    )
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
              Nothing -> tryChonologicalSplit
              Just ([], _) -> tryChonologicalSplit

              -- !! Otherwise we can progress by splitting
              Just (knownSpansAndValueMays, unknownSpans) -> Just $ (
                -- For knowns, split and try to progress the derivation.
                mconcat
                  [ let
                    newCont = mayPrevToCont prevEMay
                    newDer  = Derivation dtrace ttspan' prevDeps seenOcc newCont
                        `withDerTrace`
                          ("Split on known facts")
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
                ([], [Derivation dtrace subTspan prevDeps seenOcc contDerivation
                        `withDerTrace`
                          ("Split on unknown span or point")
                      | subTspan <- unknownSpans])
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
            | seenOcc   -> let
              dtrace' = appendDerTrace dtrace $ case occMay of
                Nothing -> "EventM is NoOcc so output no event."
                Just _ -> "EventM is (Pure _) and we've witnessed an event so output an event."
              in Just ([FactMayOcc dtrace' t occMay ], [])
            | otherwise ->  let
              dtrace' = appendDerTrace dtrace $
                "EventM is complete but we'ven not witnessed an event so output no event."
              in Just ([FactMayOcc dtrace' t Nothing], [])
          DS_SpanExc tspan -> let
            tLoMay = spanExcJustBefore tspan
            -- Clearance time iff after the start of tspan. Note that the
            -- clearance time must be in tspan or at the time just after tspan.
            -- This is a natural consequence of the fact that we observer the
            -- current Derivation as part of the calculation of clearance time.
            ctMay = clearanceTime (SomeEIx eix) tLoMay
            in case ctMay of
              Nothing -> Nothing
              Just ct ->  let
                msgCt = "Found clearance time ct=" ++ show ct ++ "."
                dtraceF = appendDerTrace dtrace $
                  msgCt ++ " This means no events are happening up to at least that time."
                in Just
                ( [FactNoOcc dtraceF (spanExc tLoMay ct)]
                -- If ct is not Inf (i.e. Nothing) and is within the current
                -- jurisdiction (i.e. tspan), then we need to cover the
                -- clearance time at and after ct.
                , case ct of
                    Just ctPoint | tspan `contains` ctPoint
                      -> [ Derivation dtrace (DS_Point ctPoint) prevDeps seenOcc contDerivation
                            `withDerTrace`
                              (msgCt ++ " Solve at the clearance time.")
                         , AfterClearanceTime
                            dtrace
                            (spanExc ct (spanExcJustAfter tspan))
                            prevDeps
                            contDerivation
                            `withDerTrace`
                              (msgCt ++ " Solve for after the clearance time")
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
            dtrace
            (DS_SpanExc concreteTimeSpan)
            []
            -- ^ NOTE [DeriveAfterFirstOcc and PrevE deps] There are
            -- no PrevE events by denotation of DeriveAfterFirstOcc
            False
            cont
              `withDerTrace`
              ("Found first occ at t=" ++ show firstOccTime)
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
               in DeriveAfterFirstOcc dtrace tspanBefore eixB cont
                  `withDerTrace`
                  ("First occ is at or before " ++ show clearanceTime
                  ++ ". Continue looking for first event before that time.")

            , Derivation dtrace (DS_Point clearanceTime) [] seenOcc cont
                  `withDerTrace`
                  ("First occ is at or before " ++ show clearanceTime
                  ++ ". Solve at that time.")
            -- See NOTE [DeriveAfterFirstOcc and PrevE deps]

            , let Just tspanAfter = tspan `intersect` RightSpaceExc clearanceTime
               in Derivation dtrace (DS_SpanExc tspanAfter) [] seenOcc cont
                  `withDerTrace`
                  ("First occ is at or before " ++ show clearanceTime
                  ++ ". Solve after that time.")
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
        Known True -> Just ([], [Derivation dtrace(DS_SpanExc tspan) prevDeps False contDer
          `withDerTrace` ("All PrevE deps are known to NOT occur. Continue solving chronologically.")
          ])
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

      -- where
      -- derivationDbg = (show eix) ++ " " ++ case derivation of
      --   Derivation _ ttspan prevDeps seenOcc _
      --     -> "Derivation ("
      --     ++ show ttspan ++ ") "
      --     ++ show prevDeps ++ " "
      --     ++ show seenOcc
      --   DeriveAfterFirstOcc _ tspan dep _
      --     -> "DeriveAfterFirstOcc ("
      --     ++ show tspan ++ ") ("
      --     ++ show dep ++ ")"
      --   AfterClearanceTime _ ct deps _
      --     -> "AfterClearanceTime "
      --     ++ show ct ++ " "
      --     ++ show deps

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
          (FactNoOcc dtrace _, DS_SpanExc tspan') -> FactNoOcc dtrace tspan'
          (FactNoOcc dtrace _, DS_Point t'   ) -> FactMayOcc dtrace t' Nothing
          (FactMayOcc _ _ _   , DS_SpanExc _) -> error "Intersection between SpanExc and Time must be Just Time or Nothing"
          (FactMayOcc dtrace _ occMay, DS_Point t') -> FactMayOcc dtrace t' occMay
        | fact <- facts
        , Just ttspan' <- [factTSpan fact `intersect` tspan]
        ]
    knownTSpans = factTSpan <$> knownFacts
    unknownTSpans = tspan `difference` knownTSpans
    in (knownFacts, unknownTSpans)



{- APPENDIX -}

  -- TODO

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

  withDerTrace
    :: Derivation a
    -- ^ Derivation (without a trace entry for the latest step) trace
    -> String
    -- ^ Msg describing most recent step taken in derivation.
    -> Derivation a
    -- ^ Derivation with added traced entry.
  withDerTrace d msg = case d of
    Derivation oldTrace ttspan prevDeps occSeen cont
      -> let dMsg = "Derivation "
                  ++ showTtspan ttspan ++ " "
                  ++ (if null prevDeps
                      then ""
                      else "(t ≤ first occ of " ++ show prevDeps ++ ") ")
                  ++ (if occSeen then "OccSeen " else " ")
                  ++ "cont=" ++ showPeakEventM cont
                  ++ ": " ++ msg
          in Derivation (oldTrace `appendDerTrace` dMsg) ttspan prevDeps occSeen cont

    DeriveAfterFirstOcc oldTrace tspan dep cont
      -> let dMsg = "After first occ of " ++ show dep
                  ++ " s.t. t∈" ++ show tspan ++ " "
                  ++ "cont=" ++ showPeakEventM cont
                  ++ ": " ++ msg
          in DeriveAfterFirstOcc (oldTrace `appendDerTrace` dMsg) tspan dep cont

    AfterClearanceTime oldTrace tspan prevDeps cont
      -> let
          dMsg = "If no PrevE deps " ++ show prevDeps ++ " occur at t=" ++ show ct ++ ": "
                  ++ show tspan
                  ++ "cont=" ++ showPeakEventM cont
                  ++ ": " ++ msg
          Just ct = spanExcJustBefore tspan
          in AfterClearanceTime (oldTrace `appendDerTrace` dMsg) tspan prevDeps cont
    where
    showTtspan (DS_Point t) = "t=" ++ show t
    showTtspan (DS_SpanExc tspan) = "t∈" ++ show tspan

    showPeakEventM :: EventM a -> String
    showPeakEventM (Pure _) = "Pure{}"
    showPeakEventM NoOcc = "NoOcc"
    showPeakEventM (GetE ix _) = "(GetE " ++ show ix ++ " _)"
    showPeakEventM (PrevE ix _) = "(PrevE " ++ show ix ++ " _)"