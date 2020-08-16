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
  import qualified Data.Set as S
  import Safe
  import Unsafe.Coerce

  import Time
  import TimeSpan
  import Timeline (TimeSpan(..))

  type DerivationTraceEl a = String
  type DerivationTrace a = [DerivationTraceEl a]
  appendDerTrace :: DerivationTrace a -> DerivationTraceEl a -> DerivationTrace a
  appendDerTrace = flip (:)

  data Fact a
    = Fact_NoOcc (DerivationTrace a) TimeSpan
    | Fact_Occ   (DerivationTrace a) Time    a

  factTSpan :: Fact a -> TimeSpan
  factTSpan (Fact_NoOcc _ tspan) = tspan
  factTSpan (Fact_Occ _ t _) = DS_Point t

  factTrace :: Fact a -> DerivationTrace a
  factTrace (Fact_NoOcc tr _) = tr
  factTrace (Fact_Occ tr _ _) = tr

-- We have some set of `EIx`s, 𝔼, and a definition for each: either a source
-- event or derived event. We want to calculate all facts about the derived
-- events from the source events.

  data InputEl = forall a . InputEl (EIx a) (Either [Fact a] (ValueM a))
  type Inputs = [InputEl]

  newtype MaybeOcc a = MaybeOcc { maybeOccToMaybe :: Maybe a }
    deriving newtype (Eq, Ord, Show, Read, Functor, Applicative, Monad)
  pattern Occ :: a -> MaybeOcc a
  pattern Occ a = MaybeOcc (Just a)
  pattern NoOcc :: MaybeOcc a
  pattern NoOcc = MaybeOcc Nothing
  {-# COMPLETE Occ, NoOcc #-}

  newtype EIx (a :: Type) = EIx { unEIx :: Int}     -- Index of an event
    deriving newtype (Eq, Ord, Show, Hashable)

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

  getE :: EIx a -> ValueM (MaybeOcc a)
  getE eix = GetE eix (Pure . Occ)

  requireE :: EIx a -> ValueM a
  requireE eix = GetE eix Pure

  -- | Note that this returns Nothing if there is no previous event
  prevV :: EIx a -> ValueM (Maybe a)
  prevV eix = PrevV eix (Pure . Occ)

  -- | Note that this returns Nothing if there is no current/previous event
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

  lookupV :: Time -> EIx a -> [SomeValueFact] -> MaybeKnown (MaybeOcc a)
  lookupV t eix facts = fmap
    (\case
      Fact_NoOcc _ _   -> NoOcc
      Fact_Occ   _ _ v -> Occ v
    )
    (lookupVFact t eix facts)

  lookupVTrace :: Time -> EIx a -> [SomeValueFact] -> MaybeKnown (DerivationTrace a)
  lookupVTrace t eix facts = factTrace <$> lookupVFact t eix facts

  lookupVFact :: Time -> EIx a -> [SomeValueFact] -> MaybeKnown (Fact a)
  lookupVFact t eix facts = MaybeKnown $ listToMaybe $
    filter ((`intersects` t) . factTSpan) (factsV' eix facts)

-- We store a knowledge base:

  data SomeValueFact = forall a . SomeValueFact (EIx a) (Fact a)
  data SomeDerivation = forall a . SomeDerivation (EIx a) (Derivation a)

  data KnowledgeBase = KnowledgeBase [SomeValueFact] [SomeDerivation]

  factsV :: EIx a -> KnowledgeBase -> [Fact a]
  factsV eix (KnowledgeBase es _)
    = factsV' eix es

  factsV' :: EIx a -> [SomeValueFact] -> [Fact a]
  factsV' (EIx eix) es
    = [ unsafeCoerce fact
      | SomeValueFact (EIx eix') fact <- es
      , eix == eix'
      ]

-- A derivation is a partial evaluation of the `deriveE` function, universally
-- quantified over a range of time.

  startDerivationForAllTime :: ValueM a -> Derivation a
  startDerivationForAllTime em = Derivation [] (DS_SpanExc allT) [] em False

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

    -- -- | DS_SpanExc tspan ⟹ t ∈ tspan
    -- DS_SpanExcInc SpanExcInc

    -- -- | DS_SpanExcIncFirstOcc lo  ⟹ t ∈ tspan
    -- forall a . DS_SpanExcIncFirstOcc SpanExc (EIx a)

-- Now a natural fist attempt at a solution is obvious: start with an initial
-- knowledge base and continue evaluating derivations until all terminate or
-- deadlock:

  solution1 :: Inputs -> KnowledgeBase
  solution1 inputs = iterateUntilChange initialKb
    where
    initialFacts = concat
      [ SomeValueFact eix <$> eventFacts
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
            ( (SomeValueFact eix <$> newFacts) ++ facts'
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
      -> [SomeValueFact]
      -- ^ Current facts. Used to query for existing facts
      -> Derivation a
      -- ^ Derivation to step
      -> Maybe ([Fact a], [Derivation a])
      -- ^ Nothing if no progress. Else Just the new facts and new derivations.
    stepDerivation eix allDerivations facts derivation = case derivation of
      Derivation dtrace ttspan prevDeps contDerivation seenOcc -> case contDerivation of
        Pure NoOcc -> if null prevDeps
          then let
                dtrace' = appendDerTrace dtrace $
                  "Pure NoOcc (t=" ++ show ttspan ++ ")."
                in Just ([Fact_NoOcc dtrace' ttspan], [])
          else stepCompleteNoOccWithPrevDeps
        Pure (Occ a) -> case ttspan of
          DS_SpanExc _ -> error "seenOcc=True when jurisdiction is not a point"
          DS_Point t -> let
                  dtrace' = appendDerTrace dtrace $
                    "Jurisdiction is a point (t=" ++ show t ++ "), ValueM is `Pure a`."
                  in Just ([Fact_Occ dtrace' t a], [])
        GetE eixb cont -> let
          factsBAndUnknownsMay = if null prevDeps
            then Just (spanLookupVFacts ttspan eixb facts)
            -- chronological version of the above with PrevV deps.
            -- TODO this and the above "then" and also the PrevV cases
            -- have very similar code (split on other facts). Try to DRY
            -- it.

            else case find isChronological (fst (spanLookupVFacts ttspan eixb facts)) of
              Nothing -> Nothing
              Just fact -> Just ([fact], ttspan `difference` factTSpan fact)

          isChronological :: Fact b -> Bool
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
                    Fact_NoOcc _ subTspan -> let
                      newCont = cont NoOcc
                      newDer  = Derivation dtrace subTspan prevDeps newCont seenOcc
                                  `withDerTrace`
                                  ("Split on GetE dep (" ++ show eixb ++ ") Fact_NoOcc")
                      in fromMaybe
                        -- Couldn't progress further: no new facts, but we've progressed the derivation up to newDer.
                        ([], [newDer])
                        -- Try to progress further.
                        (stepDerivation eix allDerivations facts newDer)
                    Fact_Occ _ t valB -> let
                        newCont = cont (Occ valB)
                        newDer  = Derivation dtrace (DS_Point t) prevDeps newCont True
                                  `withDerTrace`
                                  ("Split on GetE dep (" ++ show eixb ++ ") Fact_Occ")
                        in fromMaybe
                          ([], [newDer])
                          (stepDerivation eix allDerivations facts newDer)
                  | factB <- factsB
                  ]
                <>
                -- For unknowns, simply split the derivation into the
                -- unknown subspans.
                ( []
                , [ Derivation dtrace subTspan prevDeps contDerivation seenOcc
                    `withDerTrace`
                    ("Split on GetE dep (" ++ show eixb ++ ") unknown point or span.")
                  | subTspan <- unknowns
                  ]
                )
              )

        PrevV eixB mayPrevToCont -> case ttspan of
          -- For reference:
          --   deriveEgo t (PrevV eixB cont)
          --   = if ∃ t'  .  t' < t
          --        ∧  isJust (lookupV t' exiB)
          --        ∧  (∀ t' < t'' < t  .  lookupV t'' exiB == Nothing)
          --     then deriveEgo t (cont (lookupV t' exiB))
          --     else Nothing
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
            -- return the new Fact(s) and any new Derivation(s)
        stepCompleteNoOccWithPrevDeps = case ttspan of

          -- If the ttspan is a point time, then this is easy! Pure x means x.
          DS_Point _ -> let
              dtrace' = appendDerTrace dtrace $
                "ValueM is (Pure NoOcc). As jurisdiction is a point, we can ignore PrevV deps."
              in Just ([Fact_NoOcc dtrace' ttspan], [])

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
                  ( [Fact_NoOcc dtraceF (DS_SpanExc $ spanExc tLoMay ct)]
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
          -- Just Nothing: Fact found that goes to infinity
          -- Just t: Fact found that ends at time t (exclusive)
          neighborsAndClearanceByFacts
            :: SomeEIx
            -> Maybe (Maybe Time)
          neighborsAndClearanceByFacts ix = findClearanceAfter tLo
            where
            findClearanceAfter :: Maybe Time -> Maybe (Maybe Time)
            findClearanceAfter t = listToMaybe
              [ spanExcJustAfter tspan
              | SomeValueFact ix'' (Fact_NoOcc _ (DS_SpanExc tspan)) <- facts -- Must be a DS_SpanExc if we're looking just after a Time t.
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
          neighborsAndClearanceByDerivation ix = listToMaybe
            [ (neighbors, spanExcJustAfter tspan)
            | SomeDerivation
                ix''
                (Derivation
                  _
                  (DS_SpanExc tspan)
                  neighbors
                  (Pure _)
                  _
                )
                <- allDerivations
            , ix == SomeEIx ix'' -- look up the correct eix
            , spanExcJustBefore tspan == tLo -- starts at tLo
            ]

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
            False
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
  -- at the very start of the tspan (i.e. a Fact_NoOcc with a span at the
  -- start of tspan) doesn't count as a change.
  searchForFirstChange
    :: SpanExc
    -- ^ Time span to lookup
    -> EIx a
    -- ^ Event to lookup
    -> [SomeValueFact]
    -- ^ All known facts.
    -> FirstValueChange
  searchForFirstChange tspan eix allFacts = let
    (facts, unknownDSpans) = spanLookupVFacts (DS_SpanExc tspan) eix allFacts
    firstKnownTChangeMay     = minimumMay [ t | Fact_Occ _ t _  <- facts]

    in case firstKnownTChangeMay of
      Nothing -> if null unknownDSpans
        then NoChangeInSpan
        else Other
      Just t
        | any (intersects (fromJust $ tspan `intersect` (LeftSpaceExc t))) unknownDSpans -> FirstChangeIsAtOrBefore t
        | otherwise -> FirstChangeIsAt t

  -- | Directly look up the previous value that satisfies the predicate
  -- (strictly before the given time).
  lookupPrevV
    :: Time
    -- ^ Time t
    -> EIx a
    -- ^ Event to lookup.
    -> [SomeValueFact]
    -- ^ Known facts.
    -> MaybeKnown (Maybe a)
    -- ^ Unknown: if unknown
    -- Known Nothing: if no value satisfying the predicate occurs strictly before t.
    -- Known (Just a): the latest (projected) value satisfying the predicate (strictly before time t).
  lookupPrevV t eix allFacts = MaybeKnown . listToMaybe $ mapMaybe
        (\case
          Fact_NoOcc _ (DS_SpanExc tspan)
            -- The fact spans just before time t
            | tspan `contains` t || Just t == spanExcJustAfter tspan
            -> case spanExcJustBefore tspan of
                  Nothing -> Just Nothing
                  Just tLo -> maybeKnownToMaybe $ lookupCurrV tLo eix allFacts
            | otherwise -> Nothing
          Fact_NoOcc _ (DS_Point _) -> Nothing
          Fact_Occ _ _ _ -> Nothing
        )
        (factsV' eix allFacts)


    -- factSpanExcs = mapMaybe factSpa
    --     (\case
    --       Fact_Occ _ _ _ -> Nothing
    --       Fact_NoOcc _ tspan _ -> Just tspan
    --     )
    --     (factsV' eix allFacts)
    -- -- We must find a Fact_Occ just before or containing t.
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
    -> [SomeValueFact]
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
        Fact_NoOcc _ (DS_SpanExc tspan) -> case spanExcJustBefore tspan of
            Nothing -> Known Nothing
            Just t' -> lookupCurrV t' eix allFacts
        Fact_NoOcc _ (DS_Point _) -> lookupPrevV t eix allFacts
        Fact_Occ _ _ a -> Known (Just a)


  -- | Directly lookup the previous value for an event over a span of time.
  spanLookupPrevV
    :: TimeSpan
    -- ^ Time or span to lookup
    -> EIx a
    -- ^ Event to lookup
    -> [SomeValueFact]
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
    -> [SomeValueFact]
    -- ^ All known facts.
    -> [(TimeSpan, Maybe a)]
    -- ^ All known previous event values (if one exists)
  prevVFacts eix allFacts = concat
    [ case fact of
      Fact_NoOcc _ (DS_SpanExc tspan) -> let
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
      Fact_NoOcc _ (DS_Point _) -> []
      Fact_Occ _ _ _ -> []

    | fact <- factsV' eix allFacts
    ]

  -- | Directly look up all known facts for a given EIx and time or time
  -- span.
  spanLookupVFacts
    :: TimeSpan
    -- ^ Time or span to lookup
    -> EIx a
    -- ^ Event to lookup
    -> [SomeValueFact]
    -- ^ All known facts.
    -> ([Fact a], [TimeSpan])
    -- ^ ( Facts about the given EIx
    --   , unknown times and time spans )
    --   The union of these facts and times and time spans should exactly
    --   equal the input time/time span.
  spanLookupVFacts tspan eix allFacts = let
    facts = factsV' eix allFacts
    knownFacts =
        [ case (fact, ttspan') of
          (Fact_NoOcc dtrace _, DS_SpanExc tspan') -> Fact_NoOcc dtrace (DS_SpanExc tspan')
          (Fact_NoOcc dtrace _, DS_Point   t'    ) -> Fact_NoOcc dtrace (DS_Point t')
          (Fact_Occ _ _ _   , DS_SpanExc _) -> error "Intersection between SpanExc and Time must be Just Time or Nothing"
          (Fact_Occ dtrace _ occMay, DS_Point t') -> Fact_Occ dtrace t' occMay
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

    where
    showTtspan (DS_Point t) = "t=" ++ show t
    showTtspan (DS_SpanExc tspan) = "t∈" ++ show tspan

    showPeakValueM :: ValueM a -> String
    showPeakValueM (Pure _) = "Pure{}"
    showPeakValueM (GetE ix _) = "(GetE " ++ show ix ++ " _)"
    showPeakValueM (PrevV ix _) = "(PrevV " ++ show ix ++ " _ _)"