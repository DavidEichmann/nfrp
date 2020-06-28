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
  import Data.List (find, foldl', sortBy)
  import Data.Function (on)
  import Data.Maybe (fromMaybe, listToMaybe, mapMaybe, maybeToList, fromJust)
  import qualified Data.Set as S
  import Safe
  import Unsafe.Coerce

  import Time
  import TimeSpan

  type DerivationTraceEl a = String
  type DerivationTrace a = [DerivationTraceEl a]
  appendDerTrace :: DerivationTrace a -> DerivationTraceEl a -> DerivationTrace a
  appendDerTrace = flip (:)

  data ValueFact a
    = Fact_SpanExc (DerivationTrace a) SpanExc a
    | Fact_Point   (DerivationTrace a) Time    a

  -- type EventFact a = ValueFact (MaybeOcc a)  -- ^ Invariant: all Fact_SpanExc have `Nothing` values.

  factTSpan :: ValueFact a -> DerivationSpan
  factTSpan (Fact_SpanExc _ tspan _) = DS_SpanExc tspan
  factTSpan (Fact_Point _ t _) = DS_Point t

  factTrace :: ValueFact a -> DerivationTrace a
  factTrace (Fact_SpanExc tr _ _) = tr
  factTrace (Fact_Point tr _ _) = tr

-- We have some set of `VIx`s, 𝔼, and a definition for each: either a source
-- event or derived event. We want to calculate all facts about the derived
-- events from the source events.

  data InputEl = forall a . InputEl (VIx a) (Either [ValueFact a] (ValueM a))
  type Inputs = [InputEl]

  newtype MaybeOcc a = MaybeOcc { maybeOccToMaybe :: Maybe a }
    deriving newtype (Eq, Ord, Show, Read, Functor, Applicative, Monad)
  pattern Occ :: a -> MaybeOcc a
  pattern Occ a = MaybeOcc (Just a)
  pattern NoOcc :: MaybeOcc a
  pattern NoOcc = MaybeOcc Nothing
  {-# COMPLETE Occ, NoOcc #-}

  newtype VIx (a :: Type) = VIx Int     -- Index of an event
    deriving newtype (Eq, Ord, Show, Hashable)

  data SomeVIx = forall a . SomeVIx (VIx a)

  instance Eq SomeVIx where (SomeVIx (VIx a)) == (SomeVIx (VIx b)) = a == b
  instance Ord SomeVIx where compare (SomeVIx (VIx a)) (SomeVIx (VIx b)) = compare a b
  instance Show SomeVIx where show (SomeVIx eix) = show eix
  instance Hashable SomeVIx where
    hash (SomeVIx a) = hash a
    hashWithSalt i (SomeVIx a) = hashWithSalt i a

-- Derived events are expressed with the ValueM monad:

  data ValueM a
    = Pure a
    | forall b   . GetV  (VIx b)
                         (b -> ValueM a)
    | forall b c . PrevV (VIx b)
                         (b -> Maybe c)  -- ^ Predicate / projection.
                         (Maybe c -> ValueM a)

  deriving instance Functor ValueM

  instance Applicative ValueM where
    (<*>) = M.ap
    pure = return

  instance Monad ValueM where
    return = Pure
    fa >>= fmb = case fa of
      Pure a -> fmb a
      GetV  eixb cont -> GetV  eixb ((>>= fmb) . cont)
      PrevV eixb predicate mayPrevToCont -> PrevV eixb predicate ((>>= fmb) . mayPrevToCont)

  getV :: VIx a -> ValueM a
  getV eix = GetV eix Pure

  -- | Note that this returns Nothing at time -Inf
  prevV :: VIx a -> ValueM (Maybe a)
  prevV eix = prevVWhere eix Just

  prevVWhere :: VIx a -> (a -> Maybe b) -> ValueM (Maybe b)
  prevVWhere eix predicate = PrevV eix predicate Pure

  -- | Previous event occurrence (with initial value).
  prevE :: a -> VIx (MaybeOcc a) -> ValueM a
  prevE val0 eix = do
    prevValMay <- prevVWhere eix maybeOccToMaybe
    return (fromMaybe val0 prevValMay)


-- and a useful helper: TODO or we can just use MonadFail and a mono local bind

  onEvent :: VIx (MaybeOcc a) -> (a -> ValueM b) -> ValueM (MaybeOcc b)
  onEvent eix withA = do
    mayE <- getV eix
    case mayE of
      NoOcc -> return NoOcc
      Occ a -> Occ <$> withA a

-- Give some `inputs :: Inputs`, we have this denotation for an event/ValueM:

  -- lookupV :: Time -> VIx a -> MaybeOcc a
  -- lookupV t eix = case inputs eix of
  --   Left lookupSourceE -> lookupSourceE t
  --   Right eventM -> deriveE t eventM

  -- deriveE :: forall a . Time -> ValueM a -> MaybeOcc a
  -- deriveE t eventM = deriveEgo t eventM
  --
  -- deriveEgo :: Time -> ValueM a -> a
  -- deriveEgo t (Pure a) = a
  -- deriveEgo t (GetV eixB cont) = deriveEgo t (cont (lookupV t eixB))
  -- deriveEgo t (PrevV eixB predicate cont) =
  --   = if ∃ t'  .  t' < t
  --        ∧  isJust (predicate (lookupV t' exiB))
  --        ∧  (∀ t' < t'' < t  .  predicate (lookupV t'' exiB) == Nothing)
  --     then deriveEgo t (cont (lookupV t' exiB))
  --     else Nothing

  newtype MaybeKnown a = MaybeKnown { maybeKnownToMaybe :: Maybe a }
    deriving newtype (Eq, Ord, Show, Read, Functor, Applicative, Monad)
  pattern Known :: a -> MaybeKnown a
  pattern Known a = MaybeKnown (Just a)
  pattern Unknown :: MaybeKnown a
  pattern Unknown = MaybeKnown Nothing
  {-# COMPLETE Known, Unknown #-}

  lookupVKB :: Time -> VIx a -> KnowledgeBase -> MaybeKnown a
  lookupVKB t eix (KnowledgeBase facts _) = lookupV t eix facts

  lookupVKBTrace :: Time -> VIx a -> KnowledgeBase -> MaybeKnown (DerivationTrace a)
  lookupVKBTrace t eix (KnowledgeBase facts _) = lookupVTrace t eix facts

  lookupV :: Time -> VIx a -> [SomeValueFact] -> MaybeKnown a
  lookupV t eix facts = fmap
    (\case
      Fact_SpanExc _ _ v -> v
      Fact_Point   _ _ v -> v
    )
    (lookupVFact t eix facts)

  lookupVTrace :: Time -> VIx a -> [SomeValueFact] -> MaybeKnown (DerivationTrace a)
  lookupVTrace t eix facts = factTrace <$> lookupVFact t eix facts

  lookupVFact :: Time -> VIx a -> [SomeValueFact] -> MaybeKnown (ValueFact a)
  lookupVFact t eix facts = MaybeKnown $ listToMaybe $
    filter ((`intersects` t) . factTSpan) (factsV' eix facts)

-- We store a knowledge base:

  data SomeValueFact = forall a . SomeValueFact (VIx a) (ValueFact a)
  data SomeDerivation = forall a . SomeDerivation (VIx a) (Derivation a)

  data KnowledgeBase = KnowledgeBase [SomeValueFact] [SomeDerivation]

  factsV :: VIx a -> KnowledgeBase -> [ValueFact a]
  factsV eix (KnowledgeBase es _)
    = factsV' eix es

  factsV' :: VIx a -> [SomeValueFact] -> [ValueFact a]
  factsV' (VIx eix) es
    = [ unsafeCoerce fact
      | SomeValueFact (VIx eix') fact <- es
      , eix == eix'
      ]

-- A derivation is a partial evaluation of the `deriveE` function, universally
-- quantified over a range of time.

  startDerivationForAllTime :: ValueM a -> Derivation a
  startDerivationForAllTime em = Derivation [] (DS_SpanExc allT) [] em

  -- eix :: Eix a  is implicit
  data Derivation a
    -- When `derPrevTspan /= []` we solve in strictly chronological order.
    --
    -- ∀ t ∈ ttspan   (t <= min_{p ∈ derPrevDeps} {firstChangeTime(p, ttspan)}   when derPrevDeps /= [])
    --     . lookup t eix = deriveEgo t contDerivation
    = Derivation
      { derTrace :: DerivationTrace a
      , derTtspan :: DerivationSpan
      -- ^ Time span/point of jurisdiction.
      , derPrevDeps :: [SomeVIx]
      -- ^ dependencies via PrevV
      , derContDerivation :: ValueM a
      }

    -- ∀ t ∈ tspan (t > firstChangeTime(dep, tspan))
    --     . lookup t eix = deriveEgo t contDerivation
    | forall b . DeriveAfterFirstChange
      { derTrace :: DerivationTrace a
      , derAfterTspan   :: SpanExc
      , derAfterDep   :: VIx b
      , derAfterContDerivation :: ValueM a
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
    -- | forall a . DS_SpanExcIncFirstOcc SpanExc (VIx a)

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
      .  VIx a
      -- ^ Event index that the derivation corresponds to.
      -> [SomeDerivation]
      -- ^ Current derivations. Used to detect PrevV deadlock.
      -> [SomeValueFact]
      -- ^ Current facts. Used to query for existing facts
      -> Derivation a
      -- ^ Derivation to step
      -> Maybe ([ValueFact a], [Derivation a])
      -- ^ Nothing if no progress. Else Just the new facts and new derivations.
    stepDerivation eix allDerivations facts derivation = case derivation of
      Derivation dtrace ttspan prevDeps contDerivation -> case contDerivation of
        Pure a -> if null prevDeps
          then Just $ case ttspan of
              DS_Point t -> let
                dtrace' = appendDerTrace dtrace $
                  "Jurisdiction is a point (t=" ++ show t ++ "), ValueM is `Pure a`."
                in ([Fact_Point dtrace' t a], [])

              DS_SpanExc tspanSpan -> let
                dtrace' = appendDerTrace dtrace $
                  "Jurisdiction is (" ++ show tspanSpan ++ "), ValueM is `Pure a`."
                in ([Fact_SpanExc dtrace' tspanSpan a], [])
          else stepCompleteWithPrevDeps a
        GetV eixb cont -> let
          factsBAndUnknownsMay = if null prevDeps
            then Just (spanLookupVFacts ttspan eixb facts)
            -- chronological version of the above with PrevV deps.
            -- TODO this and the above "then" and also the PrevV cases
            -- have very similar code (split on other facts). Try to DRY
            -- it.

            else case find isChronological (fst (spanLookupVFacts ttspan eixb facts)) of
              Nothing -> Nothing
              Just fact -> Just ([fact], ttspan `difference` factTSpan fact)

          isChronological :: ValueFact b -> Bool
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
                    Fact_SpanExc _ subTspan valB -> let
                      newCont = cont valB
                      newDer  = Derivation dtrace (DS_SpanExc subTspan) prevDeps newCont
                                  `withDerTrace`
                                  ("Split on GetV dep (" ++ show eixb ++ ") Fact_SpanExc")
                      in fromMaybe
                        ([], [newDer])
                        -- ^ Couldn't progress further: no new facts, but we've progressed the derivation up to newDer.
                        (stepDerivation eix allDerivations facts newDer)
                        -- ^ Try to progress further.
                    Fact_Point _ t valB -> let
                        newCont = cont valB
                        newDer  = Derivation dtrace (DS_Point t) prevDeps newCont
                                  `withDerTrace`
                                  ("Split on GetV dep (" ++ show eixb ++ ") Fact_Point")
                        in fromMaybe
                          ([], [newDer])
                          (stepDerivation eix allDerivations facts newDer)
                  | factB <- factsB
                  ]
                <>
                -- For unknowns, simply split the derivation into the
                -- unknown subspans.
                ( []
                , [ Derivation dtrace subTspan prevDeps contDerivation
                    `withDerTrace`
                    ("Split on GetV dep (" ++ show eixb ++ ") unknown point or span.")
                  | subTspan <- unknowns
                  ]
                )
              )

        PrevV eixB predicate mayPrevToCont -> case ttspan of
          -- For reference:
          --   deriveEgo t (PrevV eixB cont)
          --   = if ∃ t'  .  t' < t
          --        ∧  isJust (lookupV t' exiB)
          --        ∧  (∀ t' < t'' < t  .  lookupV t'' exiB == Nothing)
          --     then deriveEgo t (cont (lookupV t' exiB))
          --     else Nothing
          DS_Point t -> case lookupPrevV t eixB predicate facts of
            Unknown -> Nothing
            Known prevBMay -> Just $ let
              newCont = mayPrevToCont prevBMay
              newDer  = Derivation dtrace ttspan (SomeVIx eixB : prevDeps) newCont
                    `withDerTrace`
                    ("Use known PrevV value of dep (" ++ show eixB ++ ")")
              in fromMaybe
                ([], [newDer])
                (stepDerivation eix allDerivations facts newDer)

          -- !! The Plan
          -- !! Try and split on facts about eixB.
          DS_SpanExc tspan -> let
            prevVSpans = spanLookupPrevV ttspan eixB predicate facts
            -- | Nothing means tried chronological order, but found no fact.
            factsAndUnknownsMay = if null prevDeps
              then Just prevVSpans
              -- chronological version of the above with PrevV deps.
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
                Just tLo -> lookupCurrE tLo eixB predicate facts
              in case prevValMayIfKnown of
                Unknown -> Nothing
                Known prevValMay -> Just
                    ( []
                    , [ Derivation
                          dtrace
                          ttspan
                          (SomeVIx eixB : prevDeps)
                          (mayPrevToCont prevValMay)
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
                    newDer  = Derivation dtrace ttspan' prevDeps newCont
                        `withDerTrace`
                          ("Split on known facts")
                    in fromMaybe
                      ([], [newDer])
                      -- ^ Couldn't progress further: no new facts, but we've progressed the derivation up to newDer.
                      (stepDerivation eix allDerivations facts newDer)
                      -- ^ Try to progress further.
                  | (ttspan', prevVMay) <- knownSpansAndValueMays
                  ]
                <>
                -- For unknowns, simply split the derivation into the
                -- unknown subspans.
                ([], [Derivation dtrace subTspan prevDeps contDerivation
                        `withDerTrace`
                          ("Split on unknown span or point")
                      | subTspan <- unknownSpans])
                )

        where
        -- This is called when a derivation is complete (Pure _ or NoOcc) and
        -- there are some PrevV dependencies.
        stepCompleteWithPrevDeps
          :: a
            -- ^ The derived value (The derivation must have ended with some `Pure a`).
          -> Maybe ([ValueFact a], [Derivation a])
            -- ^ Taking into account the PrevV deps, if progress can be made,
            -- return the new ValueFact(s) and any new Derivation(s)
        stepCompleteWithPrevDeps val = case ttspan of

          -- If the ttspan is a point time, then this is easy! Pure x means x.
          DS_Point t -> let
              dtrace' = appendDerTrace dtrace $
                "ValueM is (Pure _). As jurisdiction is a point, we can ignore PrevV deps."
              in Just ([Fact_Point dtrace' t val], [])

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
            ctMay = clearanceTime (SomeVIx eix) tLoMay
            in case ctMay of
              -- We don't know the clearance time, so return Nothing.
              Nothing -> Nothing
              Just ct ->  let
                msgCt = "Found clearance time ct=" ++ show ct ++ "."
                dtraceF = appendDerTrace dtrace $
                  msgCt ++ " This means no value changes are occuring up to at least that time."
                in Just
                  ( [Fact_SpanExc dtraceF (spanExc tLoMay ct) val]
                  -- If ct is not Inf (i.e. Nothing) and is within the current
                  -- jurisdiction (i.e. tspan), then we need to cover the
                  -- clearance time at and after ct.
                  , case ct of
                      Just ctPoint | tspan `contains` ctPoint
                        -> [ Derivation dtrace (DS_Point ctPoint) prevDeps contDerivation
                              `withDerTrace`
                                (msgCt ++ " Solve at the clearance time.")
                           ]
                      _ -> []
                  )

        -- | Clearance time is some known time up to which we know the value of
        -- SomeVIx will not change. In practice the value may not change even
        -- longer, so clearance time is a conservative value based on current
        -- knowledge and derivations.
        clearanceTime
          :: SomeVIx      -- ^ Event in question
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
            :: [SomeVIx]
              -- ^ Stack of `VIx`s to visit
            -> S.Set SomeVIx
              -- ^ visited `VIx`s
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
          -- single VIx.
          neighborsAndClearance
            :: SomeVIx
            -> Maybe ([SomeVIx], Maybe Time)
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
            :: SomeVIx
            -> Maybe (Maybe Time)
          neighborsAndClearanceByFacts ix = findClearanceAfter tLo
            where
            findClearanceAfter :: Maybe Time -> Maybe (Maybe Time)
            findClearanceAfter t = listToMaybe
              [ spanExcJustAfter tspan
              | SomeValueFact ix'' (Fact_SpanExc _ tspan _) <- facts
              , ix == SomeVIx ix''
              , case t of
                  Nothing -> spanExcJustBefore tspan == Nothing
                  Just tt -> tspan `contains` tt
              ]

          -- | Get the neighbors (PrevV deps) and local clearance time of a
          -- single VIx. Only considers active Derivations, not facts.
          neighborsAndClearanceByDerivation
            :: SomeVIx
            -> Maybe ([SomeVIx], Maybe Time)
          neighborsAndClearanceByDerivation ix = listToMaybe
            [ (neighbors, spanExcJustAfter tspan)
            | SomeDerivation
                ix''
                (Derivation
                  _
                  (DS_SpanExc tspan)
                  neighbors
                  cont
                )
                <- allDerivations
            , ix == SomeVIx ix'' -- look up the correct eix
            , spanExcJustBefore tspan == tLo -- starts at tLo
            -- derivation is complete
            , case cont of
                Pure _ -> True
                _ -> False
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
            []
            -- ^ NOTE [DeriveAfterFirstChange and PrevV deps] There are
            -- no PrevV events by denotation of DeriveAfterFirstChange
            cont
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

            , Derivation dtrace (DS_Point clearanceTime) [] cont
                  `withDerTrace`
                  ("First occ is at or before " ++ show clearanceTime
                  ++ ". Solve at that time.")
            -- See NOTE [DeriveAfterFirstChange and PrevV deps]

            , let Just tspanAfter = tspan `intersect` RightSpaceExc clearanceTime
               in Derivation dtrace (DS_SpanExc tspanAfter) [] cont
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
  -- at the very start of the tspan (i.e. a Fact_SpanExc with a span at the
  -- start of tspan) doesn't count as a change.
  searchForFirstChange
    :: SpanExc
    -- ^ Time span to lookup
    -> VIx a
    -- ^ Event to lookup
    -> [SomeValueFact]
    -- ^ All known facts.
    -> FirstValueChange
  searchForFirstChange tspan eix allFacts = let
    (facts, _unknownDSpans) = spanLookupVFacts (DS_SpanExc tspan) eix allFacts
    firstKnownTChangeMay     = minimumMay [ t | Fact_Point _ t _  <- facts]
    firstKnownTSpanChangeMay = listToMaybe $ sortBy (compare `on` spanExcJustBefore)
                                          [ tspan' | Fact_SpanExc _ tspan' _  <- facts]
    in case firstKnownTSpanChangeMay of
      Nothing -> case firstKnownTChangeMay of
        Just firstKnownChangeTime -> FirstChangeIsAtOrBefore firstKnownChangeTime
        Nothing -> Other
      Just tspanFirstKnown
        | spanExcSameLowerBound tspan tspanFirstKnown -> case spanExcJustAfter tspanFirstKnown of
            Just firstChangeTime -> if tspan `contains` firstChangeTime
              then FirstChangeIsAt firstChangeTime
              else NoChangeInSpan
            Nothing -> NoChangeInSpan
        | otherwise -> case firstKnownTChangeMay of
            Just tFirst -> FirstChangeIsAtOrBefore (min tFirst tspanFirstKnownLo)
            Nothing -> FirstChangeIsAtOrBefore tspanFirstKnownLo
        where
          -- We know this exists because facts must be within tspan, and we
          -- already covered the case of firstKnownTSpanChangeMay being at the
          -- start of tspan.
          tspanFirstKnownLo = fromJust $ spanExcJustBefore tspanFirstKnown

  -- | Directly look up the previous value that satisfies the predicate
  -- (strictly before the given time).
  lookupPrevV
    :: Time
    -- ^ Time t
    -> VIx a
    -- ^ Event to lookup.
    -> (a -> Maybe b)
    -- ^ predicate / projection.
    -> [SomeValueFact]
    -- ^ Known facts.
    -> MaybeKnown (Maybe b)
    -- ^ Unknown: if unknown
    -- Known Nothing: if no value satisfying the predicate occurs strictly before t.
    -- Known (Just b): the latest (projected) value satisfying the predicate (strictly before time t).
  lookupPrevV t eix predicate allFacts = MaybeKnown . listToMaybe $ mapMaybe
        (\case
          Fact_SpanExc _ tspan a
            -- The fact spans just before time t
            | tspan `contains` t || Just t == spanExcJustAfter tspan
            -> case predicate a of
                -- The fact's value satisfies the predicate. We're done.
                Just b -> Just (Just b)
                -- The fact does not satisfy the predicate. Keep searching.
                Nothing -> case spanExcJustBefore tspan of
                  Nothing -> Just Nothing
                  Just tLo -> maybeKnownToMaybe $ lookupCurrE tLo eix predicate allFacts
            | otherwise -> Nothing
          Fact_Point _ _ _ -> Nothing
        )
        (factsV' eix allFacts)


    -- factSpanExcs = mapMaybe factSpa
    --     (\case
    --       Fact_Point _ _ _ -> Nothing
    --       Fact_SpanExc _ tspan _ -> Just tspan
    --     )
    --     (factsV' eix allFacts)
    -- -- We must find a Fact_Point just before or containing t.
    -- tspanMay = find
    --     (\tspan -> tspan `contains` t || Just t == spanExcJustAfter tspan)
    --     factSpanExcs
    -- in case tspanMay of
    --   Nothing -> Unknown
    --   Just tspan -> case spanExcJustBefore tspan of
    --     Nothing -> Known Nothing
    --     Just t' -> lookupCurrE t' eix allFacts

  -- | Directly look up the current (i.e. latest) event occurrence (equal or before the given time).
  lookupCurrE
    :: Time
    -- ^ Time t
    -> VIx a
    -- ^ Event to lookup.
    -> (a -> Maybe b)
    -- ^ predicate / projection.
    -> [SomeValueFact]
    -- ^ Known facts.
    -> MaybeKnown (Maybe b)
    -- ^ Unknown: if unknown
    -- Known Nothing: if no value satisfying the predicate occurs at or before t.
    -- Known (Just b): the latest (projected) value satisfying the predicate (at or before t).
  lookupCurrE t eix predicate allFacts = let
    factMay = find (\f -> factTSpan f `contains` t) (factsV' eix allFacts)
    in case factMay of
      Nothing -> Unknown
      Just fact -> case fact of
        Fact_SpanExc _ tspan v -> case predicate v of
          Just b -> Known (Just b)
          Nothing -> case spanExcJustBefore tspan of
            Nothing -> Known Nothing
            Just t' -> lookupCurrE t' eix predicate allFacts
        Fact_Point _ _ a -> case predicate a of
          Nothing -> lookupPrevV t eix predicate allFacts
          Just b  -> Known (Just b)


  -- | Directly lookup the previous value for an event over a span of time.
  spanLookupPrevV
    :: DerivationSpan
    -- ^ Time or span to lookup
    -> VIx a
    -- ^ Event to lookup
    -> (a -> Maybe b)
    -- ^ predicate / projection.
    -> [SomeValueFact]
    -- ^ All known facts.
    -> ([(DerivationSpan, Maybe b)], [DerivationSpan])
    -- ^ ( Known values about the given VIx
    --   , unknown times and time spans )
    --   The union of these times and time spans should exactly
    --   equal the input time/time span.
  spanLookupPrevV tspan eix predicate allFacts = let
    facts = prevVFacts eix predicate allFacts
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
    :: forall a b
    .  VIx a
    -- ^ Event to lookup
    -> (a -> Maybe b)
    -- ^ predicate / projection.
    -> [SomeValueFact]
    -- ^ All known facts.
    -> [(DerivationSpan, Maybe b)]
    -- ^ All known previous event values (if one exists)
  prevVFacts eix predicate allFacts = concat
    [ case fact of
      Fact_SpanExc _ tspan _ -> let
        mayPrevVMay :: MaybeKnown (Maybe b)
        mayPrevVMay = case spanExcJustBefore tspan of
          -- Span starts at -∞ so that's a known Nothing previous event
          Nothing -> Known Nothing
          -- Span starts at a time prevT
          Just prevT -> lookupCurrE prevT eix predicate allFacts
        in case mayPrevVMay of
            Unknown -> []
            Known prevVMay -> (DS_SpanExc tspan, prevVMay) : [(DS_Point nextT, prevVMay) | Just nextT <- [spanExcJustAfter tspan]]
      Fact_Point _ _ _ -> [] -- Point knowledge is handled by the above case
    | fact <- factsV' eix allFacts
    ]

  -- | Directly look up all known facts for a given VIx and time or time
  -- span.
  spanLookupVFacts
    :: DerivationSpan
    -- ^ Time or span to lookup
    -> VIx a
    -- ^ Event to lookup
    -> [SomeValueFact]
    -- ^ All known facts.
    -> ([ValueFact a], [DerivationSpan])
    -- ^ ( Facts about the given VIx
    --   , unknown times and time spans )
    --   The union of these facts and times and time spans should exactly
    --   equal the input time/time span.
  spanLookupVFacts tspan eix allFacts = let
    facts = factsV' eix allFacts
    knownFacts =
        [ case (fact, ttspan') of
          (Fact_SpanExc dtrace _ v, DS_SpanExc tspan') -> Fact_SpanExc dtrace tspan' v
          (Fact_SpanExc dtrace _ v, DS_Point   t'    ) -> Fact_Point dtrace t' v
          (Fact_Point _ _ _   , DS_SpanExc _) -> error "Intersection between SpanExc and Time must be Just Time or Nothing"
          (Fact_Point dtrace _ occMay, DS_Point t') -> Fact_Point dtrace t' occMay
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
    Derivation oldTrace ttspan prevDeps cont
      -> let dMsg = "Derivation "
                  ++ showTtspan ttspan ++ " "
                  ++ (if null prevDeps
                      then ""
                      else "(t ≤ first occ of " ++ show prevDeps ++ ") ")
                  ++ "cont=" ++ showPeakValueM cont
                  ++ ": " ++ msg
          in Derivation (oldTrace `appendDerTrace` dMsg) ttspan prevDeps cont

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
    showPeakValueM (GetV ix _) = "(GetV " ++ show ix ++ " _)"
    showPeakValueM (PrevV ix _ _) = "(PrevV " ++ show ix ++ " _ _)"