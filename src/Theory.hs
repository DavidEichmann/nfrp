{-# LANGUAGE RecordWildCards #-}
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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}

module Theory
  ( module Theory
  , TimeSpan(..)
  ) where

  import qualified Control.Monad as M
  import Control.Applicative
  import Data.Hashable
  import Data.Kind
  import Data.List (find, foldl')
  import Data.Maybe (fromMaybe, listToMaybe, mapMaybe, fromJust)
  import Data.String
  import Data.Text.Prettyprint.Doc
  import qualified Data.Set as S
  import Safe
  import Unsafe.Coerce


  import Time
  import TimeSpan
  import Data.Function (on)

  type DerivationTraceEl a = String
  type DerivationTrace a = [DerivationTraceEl a]
  appendDerTrace :: DerivationTrace a -> DerivationTraceEl a -> DerivationTrace a
  appendDerTrace = flip (:)

  data VFact a
    = VFact_NoOcc (DerivationTrace a) TimeSpan
    | VFact_Occ   (DerivationTrace a) Time    a

  data Fact a
    = Fact_VFact (VFact a)
    | Fact_DerivationClearance (DerivationTrace a)
        [SomeEIx] -- PrevV Dependencies during the clearance time span
        SpanExc   -- Clearance time span
    -- ^ This is generally used just internally and not used in `InputEl`.
    -- This corresponds to a Derivation with non-zero span jurisdiction that is
    -- is saturated (final value is calculated i.e. cont = Pure _).

  factTSpan :: VFact a -> TimeSpan
  factTSpan (VFact_NoOcc _ tspan) = tspan
  factTSpan (VFact_Occ _ t _) = DS_Point t

  factTrace :: VFact a -> DerivationTrace a
  factTrace (VFact_NoOcc tr _) = tr
  factTrace (VFact_Occ tr _ _) = tr

-- We have some set of `EIx`s, 𝔼, and a definition for each: either a source
-- event or derived event. We want to calculate all facts about the derived
-- events from the source events.

  data InputEl = forall a . InputEl
      (EIx a)
      -- ^ The event this corresponds to
      [VFact a]
      -- ^ All (initial) known facts. This is used e.g. to set the initial value
      -- of Value (i.e. Behavior) events.
      (Maybe (ValueM a))
      -- ^ Derivation for time spans not in the (initial) known facts.
  type Inputs = [InputEl]

  inputsToInitialFactsAndDerivations :: Inputs -> ([SomeFact], [SomeDerivation])
  inputsToInitialFactsAndDerivations inputs = (initialFacts, initialDerivations)
    where
    initialFacts = concat
      [ SomeFact eix . Fact_VFact <$> eventFacts
      | InputEl eix eventFacts _ <- inputs
      ]
    initialDerivations =
      [ SomeDerivation eix (mkDerivationForTimeSpan ts eventM)
      | InputEl eix initFacts (Just eventM) <- inputs
      , ts <- (allT :: TimeSpan) `difference` (factTSpan <$> initFacts)
      ]

  newtype MaybeOcc a = MaybeOcc { maybeOccToMaybe :: Maybe a }
    deriving newtype (Eq, Ord, Show, Read, Functor, Applicative, Alternative, Monad)
  pattern Occ :: a -> MaybeOcc a
  pattern Occ a = MaybeOcc (Just a)
  pattern NoOcc :: MaybeOcc a
  pattern NoOcc = MaybeOcc Nothing
  {-# COMPLETE Occ, NoOcc #-}

  isNoOcc :: MaybeOcc a -> Bool
  isNoOcc NoOcc = True
  isNoOcc _ = False

  newtype EIx (a :: Type) = EIx { unEIx :: Int}     -- Index of an event
    deriving newtype (Eq, Ord, Hashable)

  instance Show (EIx a) where
    show (EIx a) = "EIx " ++ show a

  data SomeEIx = forall a . SomeEIx (EIx a)

  instance Eq SomeEIx where (SomeEIx (EIx a)) == (SomeEIx (EIx b)) = a == b
  instance Ord SomeEIx where compare (SomeEIx (EIx a)) (SomeEIx (EIx b)) = compare a b
  instance Show SomeEIx where show (SomeEIx eix) = show eix
  instance Hashable SomeEIx where
    hash (SomeEIx a) = hash a
    hashWithSalt i (SomeEIx a) = hashWithSalt i a

-- Derived events are expressed with the ValueM monad:

  data ValueM a
    -- | Return an occurence. Must be NoOcc if no GetE has returned a Occ yet.
    -- TODO enforce this in the API e.g. by only allowing construction from an
    -- witnessed event... or Occ contains a constraint "proof" that an event is
    -- witnessed
    = Pure (MaybeOcc a)
    -- | Get current event value if occurring.
    | forall b . GetE  (EIx b)
                       (MaybeOcc b -> ValueM a)
    -- | Get previous event value strictly before current time.
    | forall b . PrevV (EIx b)
                       (Maybe b -> ValueM a)

  deriving instance Functor ValueM

  instance Applicative ValueM where
    (<*>) = M.ap
    pure = return

  instance Monad ValueM where
    return = Pure . Occ
    fa >>= fmb = case fa of
      Pure (Occ a) -> fmb a
      Pure NoOcc -> Pure NoOcc
      GetE  eixb cont -> GetE  eixb ((>>= fmb) . cont)
      PrevV eixb mayPrevToCont -> PrevV eixb ((>>= fmb) . mayPrevToCont)

  instance MonadFail ValueM where
    fail _ = Pure NoOcc

  getE :: EIx a -> ValueM (MaybeOcc a)
  getE eix = GetE eix (Pure . Occ)

  requireE :: EIx a -> ValueM a
  requireE eix = GetE eix Pure

  -- | Note that this returns Nothing if there is no previous event
  prevV :: EIx a -> ValueM (Maybe a)
  prevV eix = PrevV eix (Pure . Occ)

  -- | Note that this returns Nothing if there is no current/previous event
  -- WARNING: this uses getE which may witness an event. Higher level APIs would
  -- abstract this away. Other wise the user may get an event occurrence without
  -- expecting it because the similar prevV function never witnesses events.
  currV :: EIx a -> ValueM (Maybe a)
  currV eix = do
    currMay <- getE eix
    case currMay of
      Occ a -> return (Just a)
      NoOcc -> prevV eix

  onEvent :: EIx a -> (a -> ValueM b) -> ValueM (MaybeOcc b)
  onEvent eix withA = do
    mayE <- getE eix
    case mayE of
      NoOcc -> return NoOcc
      Occ a -> Occ <$> withA a

-- Give some `inputs :: Inputs`, we have this denotation for an event/ValueM:

  -- lookupV :: Time -> EIx a -> MaybeOcc a
  -- lookupV t eix = case lookupInputs eix inputs of
  --   Left lookupSourceE -> lookupSourceE t
  --   Right eventM -> deriveE t eventM

  -- deriveE ::  Time -> ValueM a -> MaybeOcc a
  -- deriveE t eventM = deriveEgo False t eventM

  -- deriveEgo :: Bool -> Time -> ValueM a -> MaybeOcc a
  -- deriveEgo seenE t (Pure a) = if seenE then Occ a else error "Invalid event definition"
  -- deriveEgo seenE t (GetE eixB cont) = deriveEgo t (\bMay -> cont (seenE || isJust bMay) (lookupV t eixB) bMay)
  -- deriveEgo seenE t (PrevV eixB cont)
  --   = case max t'  where  t' < t
  --        ∧  isJust (lookupV t' exiB)
  --     then deriveEgo t (cont (lookupV t' exiB))
  --     else deriveEgo t (cont Nothing)

  newtype MaybeKnown a = MaybeKnown { maybeKnownToMaybe :: Maybe a }
    deriving newtype (Eq, Ord, Show, Read, Functor, Applicative, Monad)
  pattern Known :: a -> MaybeKnown a
  pattern Known a = MaybeKnown (Just a)
  pattern Unknown :: MaybeKnown a
  pattern Unknown = MaybeKnown Nothing
  {-# COMPLETE Known, Unknown #-}

  lookupVKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
  lookupVKB t eix (KnowledgeBase facts _) = lookupV t eix facts

  lookupVKBTrace :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (DerivationTrace a)
  lookupVKBTrace t eix (KnowledgeBase facts _) = lookupVTrace t eix facts

  lookupV :: Time -> EIx a -> [SomeFact] -> MaybeKnown (MaybeOcc a)
  lookupV t eix facts = fmap
    (\case
      VFact_NoOcc _ _   -> NoOcc
      VFact_Occ   _ _ v -> Occ v
    )
    (lookupVFact t eix facts)

  lookupVTrace :: Time -> EIx a -> [SomeFact] -> MaybeKnown (DerivationTrace a)
  lookupVTrace t eix facts = factTrace <$> lookupVFact t eix facts

  lookupVFact :: Time -> EIx a -> [SomeFact] -> MaybeKnown (VFact a)
  lookupVFact t eix facts = MaybeKnown $ listToMaybe $
    filter ((`intersects` t) . factTSpan) (factsV' eix facts)

-- We store a knowledge base:

  data SomeFact = forall a . SomeFact (EIx a) (Fact a)
  data SomeVFact = forall a . SomeVFact (EIx a) (VFact a)
  data SomeDerivation = forall a . SomeDerivation (EIx a) (Derivation a)

  data KnowledgeBase = KnowledgeBase [SomeFact] [SomeDerivation]

  factsV :: EIx a -> KnowledgeBase -> [VFact a]
  factsV eix (KnowledgeBase es _)
    = factsV' eix es

  factsV' :: EIx a -> [SomeFact] -> [VFact a]
  factsV' (EIx eix) es
    = [ (unsafeCoerce :: VFact a' -> VFact a) fact
      | SomeFact (EIx eix') (Fact_VFact fact) <- es
      , eix == eix'
      ]

-- A derivation is a partial evaluation of the `deriveE` function, universally
-- quantified over a range of time.

  mkDerivationForAllTime :: ValueM a -> Derivation a
  mkDerivationForAllTime = mkDerivationForTimeSpan (DS_SpanExc allT)

  mkDerivationForTimeSpan :: TimeSpan -> ValueM a -> Derivation a
  mkDerivationForTimeSpan ts em = Derivation [] ts [] em False

  -- eix :: Eix a  is implicit
  data Derivation a
    -- When `derPrevTspan /= []` we solve in strictly chronological order.
    --
    -- ∀ t ∈ ttspan   (t <= min_{p ∈ derPrevDeps} {firstChangeTime(p, ttspan)}   when derPrevDeps /= [])
    --     . lookup t eix = deriveEgo t contDerivation
    = Derivation
      { derTrace :: DerivationTrace a
      , derTtspan :: TimeSpan
      -- ^ Time span/point of jurisdiction.
      , derPrevDeps :: [SomeEIx]
      -- ^ dependencies via PrevV
      , derContDerivation :: ValueM a
      , derSeenOcc :: Bool
      -- ^ Have we seen an occurence yet (can only be true if TTspan is a point)
      }

    -- ∀ t ∈ tspan (t > firstChangeTime(dep, tspan))
    --     . lookup t eix = deriveEgo t contDerivation
    | forall b . DeriveAfterFirstChange
      { derTrace :: DerivationTrace a
      , derAfterTspan   :: SpanExc
      , derAfterDep   :: EIx b
      , derAfterContDerivation :: ValueM a
      }

    -- if there is no event occurrences for any of the given `SomeEIx`s, then
    -- the derivation applies, else the derivation is dropped (no new
    -- facts/derivations are derived).
    | IfNoOccAt Time [SomeEIx] (Derivation a)

    -- -- | DS_SpanExc tspan ⟹ t ∈ tspan
    -- DS_SpanExcInc SpanExcInc

    -- -- | DS_SpanExcIncFirstOcc lo  ⟹ t ∈ tspan
    -- forall a . DS_SpanExcIncFirstOcc SpanExc (EIx a)

-- Now a natural fist attempt at a solution is obvious: start with an initial
-- knowledge base and continue evaluating derivations until all terminate or
-- deadlock:

  mkKnowledgeBase :: Inputs -> KnowledgeBase
  mkKnowledgeBase inputs = iterateUntilNoChange initialKb
    where
    (initialFacts, initialDerivations) = inputsToInitialFactsAndDerivations inputs
    initialKb = KnowledgeBase initialFacts initialDerivations


  insertFacts :: [SomeFact] -> KnowledgeBase -> KnowledgeBase
  insertFacts newFs (KnowledgeBase fs ds) = iterateUntilNoChange (KnowledgeBase (newFs++fs) ds)

  iterateUntilNoChange :: KnowledgeBase -> KnowledgeBase
  iterateUntilNoChange kb = let (kb', hasChanged) = stepDerivations kb
      in if hasChanged
          then iterateUntilNoChange kb'
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
          ( (SomeFact eix <$> newFacts) ++ facts'
          , (SomeDerivation eix <$> newDerivations) ++ derivations'
          , True
          )
      )
      (facts, [], False)
      derivations

  -- This is the important part that should correspond to the `deriveE`
  -- denotation.
  stepDerivation
    :: forall a
    .  EIx a
    -- ^ Event index that the derivation corresponds to.
    -> [SomeDerivation]
    -- ^ Current derivations. Used to detect PrevV deadlock.
    -> [SomeFact]
    -- ^ Current facts. Used to query for existing facts
    -> Derivation a
    -- ^ Derivation to step
    -> Maybe ([Fact a], [Derivation a])
    -- ^ Nothing if no progress. Else Just the new facts and new derivations.
  stepDerivation eix allDerivations facts derivation
    = fmap appendClearanceFact
    $ case derivation of
    Derivation dtrace ttspan prevDeps contDerivation seenOcc -> case contDerivation of
      Pure NoOcc -> if null prevDeps
        then let
              dtrace' = appendDerTrace dtrace $
                "Pure NoOcc (t=" ++ show ttspan ++ ")."
              in Just ([Fact_VFact $ VFact_NoOcc dtrace' ttspan], [])
        else stepCompleteNoOccWithPrevDeps
      Pure (Occ a) -> case ttspan of
        DS_SpanExc _ -> error "Pure (Occ _) when jurisdiction is not a point"
        DS_Point t -> let
                dtrace' = appendDerTrace dtrace $
                  "Jurisdiction is a point (t=" ++ show t ++ "), ValueM is `Pure a`."
                in Just
                    ( [Fact_VFact $ VFact_Occ dtrace' t a]
                    , [] -- jurisdiction is a point, so we are done (even if solving chronologically).
                    )
      GetE eixb cont -> let
        fromKnowns factsB = mconcat
          [ case factB of
            VFact_NoOcc _ subTspan -> let
              newCont = cont NoOcc
              newDer  = Derivation dtrace subTspan prevDeps newCont seenOcc
                          `withDerTrace`
                          ("Split on GetE dep (" ++ show eixb ++ ") VFact_NoOcc")
              in fromMaybe
                -- Couldn't progress further: no new facts, but we've progressed the derivation up to newDer.
                ([], [newDer])
                -- Try to progress further.
                (stepDerivation eix allDerivations facts newDer)
            VFact_Occ _ t valB -> let
                newCont = cont (Occ valB)
                newDer  = Derivation dtrace (DS_Point t) prevDeps newCont True
                          `withDerTrace`
                          ("Split on GetE dep (" ++ show eixb ++ ") VFact_Occ")
                in fromMaybe
                  ([], [newDer])
                  (stepDerivation eix allDerivations facts newDer)
          | factB <- factsB
          ]

        isChronological :: VFact b -> Bool
        isChronological fact = case ttspan of
          DS_Point _ -> True  -- we use the assumption that fact is in ttspan
          DS_SpanExc tspan -> case factTSpan fact of
            DS_Point _ -> False
            DS_SpanExc tspan' -> spanExcSameLowerBound tspan tspan'

        vfactsB = spanLookupVFacts ttspan eixb facts

        in if null prevDeps
          then case vfactsB of
            ([], _) -> Nothing
            (factsB, unknowns) -> Just $ (
                -- For knowns, split and try to progress the derivation.
                fromKnowns factsB
                <>
                -- For unknowns, simply split the derivation into the
                -- unknown subspans.
                ( []
                , [ Derivation dtrace subTspan prevDeps contDerivation seenOcc
                      `withDerTrace`
                      ("Split on GetE dep (" ++ show eixb ++ ") which has unknown value at " ++ show subTspan)
                  | subTspan <- unknowns
                  ]
                )
              )

          -- Solve chronologically
          else case find isChronological (fst vfactsB) of
            Nothing -> Nothing
            Just fact -> let
              -- The point and span covering the rest of the jurisdiction.
              -- Nothing if `fact` already coverse the full jurisdiction.
              nextPointMay :: Maybe (Time, SpanExc)
              nextPointMay = case factTSpan fact of
                DS_Point _ -> Nothing
                DS_SpanExc factSpanExc -> case spanExcJustAfter factSpanExc of
                  Nothing -> Nothing -- Fact already covers up until Inf
                  Just factAfterT -> case ttspan of
                    DS_Point _ -> error "Impossible! fact's ttspan must be a subset of ttspan"
                    DS_SpanExc tspan -> tspan `difference` LeftSpaceExc factAfterT
              in Just (
                -- Split on chronological fact.
                fromKnowns [fact]
                <>
                -- For unknowns, simply split the derivation into the
                -- unknown subspans.
                ( []
                , concat
                  [ -- Derive at the next point. This is always safe to do so
                    -- as the first occurrence of a PrevV dep is earliest at
                    -- this point. The derivation has jurisdiction up to and
                    -- _including_ such an occurrence.
                    [ Derivation dtrace (DS_Point t) prevDeps contDerivation seenOcc
                    -- Only if no prevV deps are occuring at time t, then we
                    -- continue chronologically past that point.
                    , IfNoOccAt t prevDeps
                        $ Derivation dtrace (DS_SpanExc tspan) prevDeps contDerivation seenOcc
                    ]
                  | Just (t, tspan) <- [nextPointMay]
                  ]
                )
              )


      PrevV eixB mayPrevToCont -> case ttspan of
        DS_Point t -> case lookupPrevV t eixB facts of
          Unknown -> Nothing
          Known prevBMay -> Just $ let
            newCont = mayPrevToCont prevBMay
            newDer  = Derivation dtrace ttspan (SomeEIx eixB : prevDeps) newCont seenOcc
                  `withDerTrace`
                  ("Use known PrevV value of dep (" ++ show eixB ++ ")")
            in fromMaybe
              ([], [newDer])
              (stepDerivation eix allDerivations facts newDer)

        -- !! The Plan
        -- !! Try and split on facts about eixB.
        DS_SpanExc tspan -> let
          prevVSpans = spanLookupPrevV ttspan eixB facts
          factsAndUnknownsMay = if null prevDeps -- If not solving chronologically
            then Just prevVSpans
            -- chronological version. Use only the first fact spanning the start of ttspan.
            else case find ((tspan `contains`) . fst) (fst prevVSpans) of
              Nothing -> Nothing
              Just knownSpanAndFact -> Just ([knownSpanAndFact], ttspan `difference` fst knownSpanAndFact)

          -- !! Split into (1) events after the first eixB event in tspan and
          -- !! (2) chronologically solving before that event.
          -- Previously we checked for deadlock and only started solving
          -- chronologically if deadlocked via eixB. This is not necessary, we
          -- can just always solve chronologically. It seems like this would
          -- fail to produce knowable facts that are not chronological, but that
          -- problem is solved by a second derivation with jurisdiction after
          -- the first occurrence of eixB. Since the previous (PrevV) value is
          -- only known for spans of NoOcc after an event occurrence, we know
          -- that chronological before the first occurrence of eixB will be
          -- productive (produce facts as soon as they are knowable).
          tryChonologicalSplit = let
            tspanLo = spanExcJustBefore tspan
            prevValMayIfKnown = case tspanLo of
              Nothing -> Known Nothing -- Known: there is no previous value.
              Just tLo -> lookupCurrV tLo eixB facts
            in case prevValMayIfKnown of
              Unknown -> Nothing
              Known prevValMay -> Just
                  ( []
                  , [ Derivation
                        dtrace
                        ttspan
                        (SomeEIx eixB : prevDeps)
                        (mayPrevToCont prevValMay)
                        seenOcc
                      `withDerTrace`
                        ("Deadlock detected via " ++ show eixB ++ " (at t=" ++ show tspanLo ++ "). Store "
                        ++ show eixB ++ " as a PrevV dep and solve chronologically")
                    , DeriveAfterFirstChange
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
            -- a PrevV dependency, we must solve chronologically (at least
            -- piecewise after known events occs).

            -- !! If there are no such facts, try to detect deadlock via
            -- !! eixB. This means that eix is reachable (transitively) via
            -- !! the PrevV dependencies of derivations coinciding with the
            -- !! start of tspan.
            Nothing -> tryChonologicalSplit
            Just ([], _) -> tryChonologicalSplit

            -- !! Otherwise we can progress by splitting
            Just (knownSpansAndValueMays, unknownSpans) -> Just $ (
              -- For knowns, split and try to progress the derivation.
              mconcat
                [ let
                  newCont = mayPrevToCont prevVMay
                  newDer  = Derivation dtrace ttspan' prevDeps newCont seenOcc
                      `withDerTrace`
                        ("Split on known facts")
                  in fromMaybe
                    -- Couldn't progress further: no new facts, but we've progressed the derivation up to newDer.
                    ([], [newDer])
                    -- Try to progress further.
                    (stepDerivation eix allDerivations facts newDer)
                | (ttspan', prevVMay) <- knownSpansAndValueMays
                ]
              <>
              -- For unknowns, simply split the derivation into the
              -- unknown subspans.
              ([], [Derivation dtrace subTspan prevDeps contDerivation seenOcc
                      `withDerTrace`
                        ("Split on unknown span or point")
                    | subTspan <- unknownSpans])
              )

      where
      -- This is called when a derivation is complete (Pure NoOcc) and
      -- there are some PrevV dependencies.
      stepCompleteNoOccWithPrevDeps
        :: Maybe ([Fact a], [Derivation a])
          -- ^ Taking into account the PrevV deps, if progress can be made,
          -- return the new VFact(s) and any new Derivation(s)
      stepCompleteNoOccWithPrevDeps = case ttspan of

        -- If the ttspan is a point time, then this is easy! Pure NoOcc means NoOcc.
        DS_Point _ -> let
            dtrace' = appendDerTrace dtrace $
              "ValueM is (Pure NoOcc). As jurisdiction is a point, we can ignore PrevV deps."
            in Just ([Fact_VFact $ VFact_NoOcc dtrace' ttspan], [])

        -- If the ttspan is a span, things get more tricky. At this point we
        -- need to find a "clearance time". This is some time span at the
        -- start of ttspan where whe know none of the PrevV deps are changing
        -- (within the time jurisdiction of this Derivation). We do this by
        -- finding the transitive closure of PrevV dependencies. For each dep
        -- we have either facts indicating for how long no there is no change,
        -- or a complete derivation, or an incomplete derivation.
        DS_SpanExc tspan -> let
          tLoMay = spanExcJustBefore tspan
          -- Clearance time iff after the start of tspan. Note that the
          -- clearance time must be in tspan or at the time just after tspan.
          -- This is a natural consequence of the fact that we observe the
          -- current Derivation as part of the calculation of clearance time.
          ctMay = clearanceTime (SomeEIx eix) tLoMay
          in case ctMay of
            -- We don't know the clearance time, so return Nothing.
            Nothing -> Nothing
            Just ct ->  let
              msgCt = "Found clearance time ct=" ++ show ct ++ "."
              dtraceF = appendDerTrace dtrace $
                msgCt ++ " This means no value changes are occuring up to at least that time."
              in Just
                ( [Fact_VFact $ VFact_NoOcc dtraceF (DS_SpanExc $ spanExc tLoMay ct)]
                -- If ct is not Inf (i.e. Nothing) and is within the current
                -- jurisdiction (i.e. tspan), then we need to cover the
                -- clearance time at ct.
                , case ct of
                    Just ctPoint
                      | tspan `contains` ctPoint
                      -> [ Derivation dtrace (DS_Point ctPoint) prevDeps contDerivation seenOcc
                            `withDerTrace`
                              (msgCt ++ " Solve at the clearance time.")
                          ]
                    _ -> []
                )

      -- | Clearance time is some known time up to which we know the value of
      -- SomeEIx will not change. In practice the value may not change even
      -- longer, so clearance time is a conservative value based on current
      -- knowledge and derivations.
      clearanceTime
        :: SomeEIx      -- ^ Event in question
        -> Maybe Time   -- ^ Start time of clearance ((exclusive) start of the span of NoOcc ). Nothing means -Inf.
        -> Maybe (Maybe Time)
                        -- ^ Clearance time if greater than the input time ((exclusive) end of the span of NoOcc). Just Nothing means Inf.
      clearanceTime ix' tLo = do
        -- Get the initial "local" clearance.
        -- local clearance is the clearance assuming that prevV dependencies never change.
        -- The clearance is min{local clearance, clearance of dependencies}
        (neighbors, ixClearanceTime) <- neighborsAndClearance ix'
        go neighbors (S.singleton ix') ixClearanceTime
        where
        go
          :: [SomeEIx]
            -- ^ Stack of `EIx`s to visit
          -> S.Set SomeEIx
            -- ^ visited `EIx`s
          -> Maybe Time
            -- ^ clearance time so far (if any).
          -> Maybe (Maybe Time)
            -- ^ clearance time if greater than input time.
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

        -- | Get the neighbors (PrevV deps) and local clearance time of a
        -- single EIx.
        neighborsAndClearance
          :: SomeEIx
          -> Maybe ([SomeEIx], Maybe Time)
        neighborsAndClearance ix
          = (([],) <$> neighborsAndClearanceByFacts ix) -- No PrevV deps if a fact.
          <|> neighborsAndClearanceByDerivation ix

        -- | Get the clearance time (ignoring neighbors) of a single value
        -- by looking for a fact spanning the time just after tLo.
        --
        -- Nothing: No fact spanning the time.
        -- Just Nothing: VFact found that goes to infinity
        -- Just t: VFact found that ends at time t (exclusive)
        neighborsAndClearanceByFacts
          :: SomeEIx
          -> Maybe (Maybe Time)
        neighborsAndClearanceByFacts ix = findClearanceAfter tLo
          where
          findClearanceAfter :: Maybe Time -> Maybe (Maybe Time)
          findClearanceAfter t = listToMaybe
            [ spanExcJustAfter tspan
            | SomeFact ix'' (Fact_VFact (VFact_NoOcc _ (DS_SpanExc tspan))) <- facts -- Must be a DS_SpanExc if we're looking just after a Time t.
            , ix == SomeEIx ix''
            , case t of
                Nothing -> spanExcJustBefore tspan == Nothing
                Just tt -> tspan `contains` tt
            ]

        -- | Get the neighbors (PrevV deps) and local clearance time of a
        -- single EIx. Only considers active Derivations, not facts.
        neighborsAndClearanceByDerivation
          :: SomeEIx
          -> Maybe ([SomeEIx], Maybe Time)
        neighborsAndClearanceByDerivation (SomeEIx ix) = lookupClearanceFact tLo ix facts

    DeriveAfterFirstChange dtrace tspan eixB cont -> case searchForFirstChange tspan eixB facts of
      -- We know the time of the first occurrence, so we can convert
      -- to a concrete time span again.
      FirstChangeIsAt firstChangeTime -> let
        -- Safe to use mono-bind here as firstChangeTime ∈ tspan
        Just concreteTimeSpan = tspan `intersect` RightSpaceExc firstChangeTime
        newDer = Derivation
          dtrace
          (DS_SpanExc concreteTimeSpan)
          -- NOTE [DeriveAfterFirstChange and PrevV deps] There are no PrevV
          -- events by denotation of DeriveAfterFirstChange
          []
          cont
          False -- We're in a span jurisdiction and haven't witnessed an event.
            `withDerTrace`
            ("Found first occ at t=" ++ show firstChangeTime)
        in Just ([], [newDer])

      -- We know the right of clearanceTime (exclusive) is definitely
      -- after the first event.
      FirstChangeIsAtOrBefore clearanceTime -> let
        newDers =
          [ let Just tspanBefore = tspan `intersect` LeftSpaceExc clearanceTime
              in DeriveAfterFirstChange dtrace tspanBefore eixB cont
                `withDerTrace`
                ("First occ is at or before " ++ show clearanceTime
                ++ ". Continue looking for first event before that time.")

          , Derivation dtrace (DS_Point clearanceTime) [] cont False
                `withDerTrace`
                ("First occ is at or before " ++ show clearanceTime
                ++ ". Solve at that time.")
          -- See NOTE [DeriveAfterFirstChange and PrevV deps]

          , let Just tspanAfter = tspan `intersect` RightSpaceExc clearanceTime
              in Derivation dtrace (DS_SpanExc tspanAfter) [] cont False
                `withDerTrace`
                ("First occ is at or before " ++ show clearanceTime
                ++ ". Solve after that time.")
          -- See NOTE [DeriveAfterFirstChange and PrevV deps]
          ]
        in Just ([], newDers)

      -- There is no first occ, so this derivation covers no time, so
      -- we stop.
      NoChangeInSpan -> Just ([], [])

      -- We don't know any more info about the first occurrence so we
      -- cant make any more progress.
      Other -> Nothing

    IfNoOccAt t deps der -> case sequence [isNoOcc <$> lookupV t depEIx facts | SomeEIx depEIx <- deps] of
      Unknown -> Nothing
      Known isNoOccs -> if and isNoOccs
        -- No dep events are occurring. Continue with the derivation.
        then Just ([], [der])
        -- One or more dep events are occurring. Stop.
        else Just ([], [])
    where
    appendClearanceFact :: ([Fact a], [Derivation a]) -> ([Fact a], [Derivation a])
    appendClearanceFact (fs, ds)
      = ( [Fact_DerivationClearance ("To Clearance Fact":tr) prevDeps tspan
            | Derivation tr (DS_SpanExc tspan) prevDeps (Pure _) _ <- ds
            , not (null prevDeps)
            ] ++ fs
        , ds
        )

  -- | Result of searching for the first change of a specific value and time
  -- span.
  data FirstValueChange
    -- | Enough information is known such that we can be sure this is the
    -- first change.
    = FirstChangeIsAt Time
    -- | Enough information is known such that we can be sure the first change
    -- is at or before this time. This time will be the first *known* value
    -- change, but there will be unknown changes before this time that may
    -- contain the true first change.
    | FirstChangeIsAtOrBefore Time
    -- | We have full information and know that no change is occurring in the
    -- searched span.
    | NoChangeInSpan
    -- | Facts are missing such that we cant say anything about the first
    -- change.
    | Other

  -- | Find the first change of value in this span. Note that a change of value
  -- at the very start of the tspan (i.e. a VFact_NoOcc with a span at the
  -- start of tspan) doesn't count as a change.
  searchForFirstChange
    :: SpanExc
    -- ^ Time span to lookup
    -> EIx a
    -- ^ Event to lookup
    -> [SomeFact]
    -- ^ All known facts.
    -> FirstValueChange
  searchForFirstChange tspan eix allFacts = let
    (facts, unknownDSpans) = spanLookupVFacts (DS_SpanExc tspan) eix allFacts
    firstKnownTChangeMay = minimumMay [ t | VFact_Occ _ t _  <- facts]

    in case firstKnownTChangeMay of
      Nothing -> if null unknownDSpans
        then NoChangeInSpan
        else Other
      Just t
        | any (intersects (fromJust $ tspan `intersect` (LeftSpaceExc t))) unknownDSpans -> FirstChangeIsAtOrBefore t
        | otherwise -> FirstChangeIsAt t

  lookupClearanceFact
    :: Maybe Time
    -- ^ Time at the start of (exclusive) the clearance (Nothing means -Inf).
    -> EIx a
    -- ^ The event in question.
    -> [SomeFact]
    -- ^ Known Facts
    -> Maybe ([SomeEIx], Maybe Time)
    -- ^ Dependencies and clearance end time (exclusive).
    -- Nothing: no clearance fact found
    -- Just (_, Nothing): Inf
    -- Just (_, Just tHi): clearance ends just before tHi
  lookupClearanceFact tLo (EIx eixInt) facts = maximumByMay (compare `on` snd)
    [ (prevVDeps, spanExcJustAfter tspan)
    | SomeFact (EIx otherEIxInt) (Fact_DerivationClearance _ prevVDeps tspan) <- facts
    , eixInt == otherEIxInt
    , spanExcJustBefore tspan == tLo
    ]

  -- | Directly look up the previous value that satisfies the predicate
  -- (strictly before the given time).
  lookupPrevV
    :: Time
    -- ^ Time t
    -> EIx a
    -- ^ Event to lookup.
    -> [SomeFact]
    -- ^ Known facts.
    -> MaybeKnown (Maybe a)
    -- ^ Unknown: if unknown
    -- Known Nothing: if no value satisfying the predicate occurs strictly before t.
    -- Known (Just a): the latest (projected) value satisfying the predicate (strictly before time t).
  lookupPrevV t eix allFacts = MaybeKnown . listToMaybe $ mapMaybe
        (\case
          VFact_NoOcc _ (DS_SpanExc tspan)
            -- The fact spans just before time t
            | tspan `contains` t || Just t == spanExcJustAfter tspan
            -> case spanExcJustBefore tspan of
                  Nothing -> Just Nothing
                  Just tLo -> maybeKnownToMaybe $ lookupCurrV tLo eix allFacts
            | otherwise -> Nothing
          VFact_NoOcc _ (DS_Point _) -> Nothing
          VFact_Occ _ _ _ -> Nothing
        )
        (factsV' eix allFacts)


    -- factSpanExcs = mapMaybe factSpa
    --     (\case
    --       VFact_Occ _ _ _ -> Nothing
    --       VFact_NoOcc _ tspan _ -> Just tspan
    --     )
    --     (factsV' eix allFacts)
    -- -- We must find a VFact_Occ just before or containing t.
    -- tspanMay = find
    --     (\tspan -> tspan `contains` t || Just t == spanExcJustAfter tspan)
    --     factSpanExcs
    -- in case tspanMay of
    --   Nothing -> Unknown
    --   Just tspan -> case spanExcJustBefore tspan of
    --     Nothing -> Known Nothing
    --     Just t' -> lookupCurrV t' eix allFacts

  -- | Directly look up the current (i.e. latest) event occurrence (equal or before the given time).
  lookupCurrV
    :: Time
    -- ^ Time t
    -> EIx a
    -- ^ Event to lookup.
    -> [SomeFact]
    -- ^ Known facts.
    -> MaybeKnown (Maybe a)
    -- ^ Unknown: if unknown
    -- Known Nothing: if no value satisfying the predicate occurs at or before t.
    -- Known (Just a): the latest occ value (at or before t).
  lookupCurrV t eix allFacts = let
    factMay = find (\f -> factTSpan f `contains` t) (factsV' eix allFacts)
    in case factMay of
      Nothing -> Unknown
      Just fact -> case fact of
        VFact_NoOcc _ (DS_SpanExc tspan) -> case spanExcJustBefore tspan of
            Nothing -> Known Nothing
            Just t' -> lookupCurrV t' eix allFacts
        VFact_NoOcc _ (DS_Point _) -> lookupPrevV t eix allFacts
        VFact_Occ _ _ a -> Known (Just a)


  -- | Directly lookup the previous value for an event over a span of time.
  spanLookupPrevV
    :: TimeSpan
    -- ^ Time or span to lookup
    -> EIx a
    -- ^ Event to lookup
    -> [SomeFact]
    -- ^ All known facts.
    -> ([(TimeSpan, Maybe a)], [TimeSpan])
    -- ^ ( Known values about the given EIx
    --   , unknown times and time spans )
    --   The union of these times and time spans should exactly
    --   equal the input time/time span.
  spanLookupPrevV tspan eix allFacts = let
    facts = prevVFacts eix allFacts
    knownFacts =
        [ (ttspan', aMay)
        | (factTspan, aMay) <- facts
        , Just ttspan' <- [factTspan `intersect` tspan]
        ]
    knownTSpans = fst <$> knownFacts
    unknownTSpans = tspan `difference` knownTSpans
    in (knownFacts, unknownTSpans)


  -- | Get all known PervV spans for an event
  prevVFacts
    :: forall a
    .  EIx a
    -- ^ Event to lookup
    -> [SomeFact]
    -- ^ All known facts.
    -> [(TimeSpan, Maybe a)]
    -- ^ All known previous event values (if one exists)
  prevVFacts eix allFacts = concat
    [ case fact of
      VFact_NoOcc _ (DS_SpanExc tspan) -> let
        mayPrevVMay :: MaybeKnown (Maybe a)
        mayPrevVMay = case spanExcJustBefore tspan of
          -- Span starts at -∞ so that's a known Nothing previous event
          Nothing -> Known Nothing
          -- Span starts at a time prevT
          Just prevT -> lookupCurrV prevT eix allFacts
        in case mayPrevVMay of
            Unknown -> []
            Known prevVMay -> (DS_SpanExc tspan, prevVMay) : [(DS_Point nextT, prevVMay) | Just nextT <- [spanExcJustAfter tspan]]

      -- Point knowledge is handled by the above case
      VFact_NoOcc _ (DS_Point _) -> []
      VFact_Occ _ _ _ -> []

    | fact <- factsV' eix allFacts
    ]

  -- | Directly look up all known facts for a given EIx and time or time
  -- span.
  spanLookupVFacts
    :: TimeSpan
    -- ^ Time or span to lookup
    -> EIx a
    -- ^ Event to lookup
    -> [SomeFact]
    -- ^ All known facts.
    -> ([VFact a], [TimeSpan])
    -- ^ ( Facts about the given EIx
    --   , unknown times and time spans )
    --   The union of these facts and times and time spans should exactly
    --   equal the input time/time span.
  spanLookupVFacts tspan eix allFacts = let
    facts = factsV' eix allFacts
    knownFacts =
        [ case (fact, ttspan') of
          (VFact_NoOcc dtrace _, DS_SpanExc tspan') -> VFact_NoOcc dtrace (DS_SpanExc tspan')
          (VFact_NoOcc dtrace _, DS_Point   t'    ) -> VFact_NoOcc dtrace (DS_Point t')
          (VFact_Occ _ _ _   , DS_SpanExc _) -> error "Intersection between SpanExc and Time must be Just Time or Nothing"
          (VFact_Occ dtrace _ occMay, DS_Point t') -> VFact_Occ dtrace t' occMay
        | fact <- facts
        , Just ttspan' <- [factTSpan fact `intersect` tspan]
        ]
    knownTSpans = factTSpan <$> knownFacts
    unknownTSpans = tspan `difference` knownTSpans
    in (knownFacts, unknownTSpans)



{- APPENDIX -}

  -- TODO

  withDerTrace
    :: Derivation a
    -- ^ Derivation (without a trace entry for the latest step) trace
    -> String
    -- ^ Msg describing most recent step taken in derivation.
    -> Derivation a
    -- ^ Derivation with added traced entry.
  withDerTrace d msg = case d of
    Derivation oldTrace ttspan prevDeps cont seenOcc
      -> let dMsg = "Derivation "
                  ++ showTtspan ttspan ++ " "
                  ++ (if null prevDeps
                      then ""
                      else "(t ≤ first occ of " ++ show prevDeps ++ ") ")
                  ++ "cont=" ++ showPeakValueM cont
                  ++ ": " ++ msg
          in Derivation (oldTrace `appendDerTrace` dMsg) ttspan prevDeps cont seenOcc

    DeriveAfterFirstChange oldTrace tspan dep cont
      -> let dMsg = "After first occ of " ++ show dep
                  ++ " s.t. t∈" ++ show tspan ++ " "
                  ++ "cont=" ++ showPeakValueM cont
                  ++ ": " ++ msg
          in DeriveAfterFirstChange (oldTrace `appendDerTrace` dMsg) tspan dep cont

    IfNoOccAt t deps der -> IfNoOccAt t deps (withDerTrace der msg)

    where
    showTtspan (DS_Point t) = "t=" ++ show t
    showTtspan (DS_SpanExc tspan) = "t∈" ++ show tspan

    showPeakValueM :: ValueM a -> String
    showPeakValueM (Pure _) = "Pure{}"
    showPeakValueM (GetE ix _) = "(GetE " ++ show ix ++ " _)"
    showPeakValueM (PrevV ix _) = "(PrevV " ++ show ix ++ " _)"



  instance Pretty (EIx a) where
    pretty = fromString . show

  instance Pretty SomeEIx where
    pretty (SomeEIx eix) = pretty eix

  instance Pretty SomeDerivation where
    pretty (SomeDerivation ix der) = pretty (ix, der)

  instance Pretty (Derivation a) where
    pretty der = case der of
      Derivation{..} -> nest 2 $ vsep
        [ "Derivation"
        , "derTrace = " <> "_" -- pretty derTrace
        , "derTtspan = " <> pretty derTtspan
        , "derPrevDeps = " <> pretty derPrevDeps
        , "derContDerivation = " <> "_" -- pretty derContDerivation
        , "derSeenOcc = " <> pretty derSeenOcc
        ]
      DeriveAfterFirstChange{..} -> nest 2 $ vsep
        [ "DeriveAfterFirstChange"
        , "derTrace = " <> "_" -- pretty derTrace
        , "derAfterTspan = " <> pretty derAfterTspan
        , "derAfterDep = " <> pretty derAfterDep
        , "derAfterContDerivation = " <> "_" -- pretty derAfterContDerivation
        ]
      IfNoOccAt t deps der' -> nest 2 $ vsep
        [ "IfNoOccAt"
        , "t = " <> pretty t
        , "deps = " <> pretty deps
        , "der = " <> pretty der'
        ]

  instance Pretty KnowledgeBase where
    pretty (KnowledgeBase _facts ders) = nest 2 $ vsep
      [ "KnowledgeBase "
      , "Facts = _" -- <> pretty facts
      , "Ders = " <> pretty ders
      ]
