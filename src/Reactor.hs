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
{-
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

import Theory
  ( ValueFact(..)
  , SomeValueFact(..)
  , VIx(..)
--   , SomeVIx(..)

  , ValueM(..)

--   , Inputs
--   , InputEl(..)

--   , MaybeOcc(..)
--   , pattern Occ
--   , pattern NoOcc

--   , MaybeKnown(..)
--   , pattern Known
--   , pattern Unknown

--   , Derivation(..)
--   , SomeDerivation(..)
--   , mkDerivationForAllTime

  , TimeSpan(..)
--   , factTSpan

--   , DerivationTrace
--   , DerivationTraceEl
--   , appendDerTrace
  )

--
-- Some key types
--

data Region a
  = Region_Fact (VIx a) TimeSpan

-- | Describes the change in knowlage after inserting one or many facts.
data Diff

data Reactor

data Reaction a
  = RPure a
  | forall b . Read  (Region b)   (b -> Reaction a)
  | forall b . Write (Region b) b (Reaction a)
  | Fork  (Reaction ()) (Reaction a)
  -- | forall b . LiftIO (IO b) (b -> Reaction a)

deriving instance Functor Reaction

instance Applicative Reaction where
  (<*>) = M.ap
  pure = return

instance Monad Reaction where
  return = RPure
  fa >>= fmb = case fa of
    RPure a -> fmb a
    Read  ix     cont -> Read  ix     ((>>= fmb) . cont)
    Write ix val cont -> Write ix val (cont >>= fmb)
    Fork  fork   cont -> Fork fork    (cont >>= fmb)
    -- LiftIO io    cont -> LiftIO io    ((>>= fmb) . cont)

read :: Region a -> Reaction a
read region = Read region RPure

write :: Region a -> a -> Reaction ()
write region value = Write region value (RPure ())

forkReaction :: Reaction () -> Reaction ()
forkReaction fork = Fork fork (RPure ())

--
-- This is the main API to create and update reactors.
--

mkReactor :: [Reaction ()] -> Reactor
mkReactor = _

insertFact :: SomeValueFact -> Reactor -> (Reactor, Diff)
insertFact = _

-- | Given a VIx and a ValueM describing it for all time, this creates a Reaction.
valueMForAllTimeToReaction :: forall a . VIx a -> ValueM a -> Reaction ()
valueMForAllTimeToReaction vix valueMTop = go (DS_SpanExc allT) valueMTop
  where
  go :: TimeSpan -> ValueM a -> Reaction ()
  go derSpan valueM = case valueM of
    Pure a -> write (Region_Fact vix derSpan) a
    GetV vixB cont -> forkOnValue vixB derSpan $ \derSpan' b -> go derSpan' (cont b)
    PrevV vixB predicate cont -> _

  -- data ValueM a
  --   = Pure a
  --   | forall b   . GetV  (VIx b)
  --                        (b -> ValueM a)
  --   | forall b c . PrevV (VIx b)
  --                        (b -> Maybe c)  -- ^ Predicate / projection.
  --                        (Maybe c -> ValueM a)

--
-- Some handy Reaction patterns
--

forkOnValue :: VIx a -> TimeSpan -> (TimeSpan -> a -> Reaction ()) -> Reaction ()
forkOnValue = _
-}


{-

data KnowledgeBase = KnowledgeBase
  { -- TODO
  }

lookupVKB :: Time -> VIx a -> KnowledgeBase -> MaybeKnown a
lookupVKB = _

lookupVKBTrace :: Time -> VIx a -> KnowledgeBase -> MaybeKnown (DerivationTrace a)
lookupVKBTrace = _

-- Now a natural fist attempt at a solution is obvious: start with an initial
-- knowledge base and continue evaluating derivations until all terminate or
-- deadlock:

mkKnowledgeBase :: Inputs -> KnowledgeBase
mkKnowledgeBase inputs = iterateUntilChange initialKb
  where
  initialFacts = concat
    [ SomeValueFact eix <$> eventFacts
    | InputEl eix (Left eventFacts) <- inputs
    ]
  initialDerivations =
    [ SomeDerivation eix (mkDerivationForAllTime eventM)
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
  stepDerivations (KnowledgeBase {} {- facts derivations -})
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
              Just tLo -> lookupCurrV tLo eixB predicate facts
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
                Just tLo -> maybeKnownToMaybe $ lookupCurrV tLo eix predicate allFacts
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
  --     Just t' -> lookupCurrV t' eix allFacts

-- | Directly look up the current (i.e. latest) event occurrence (equal or before the given time).
lookupCurrV
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
lookupCurrV t eix predicate allFacts = let
  factMay = find (\f -> factTSpan f `contains` t) (factsV' eix allFacts)
  in case factMay of
    Nothing -> Unknown
    Just fact -> case fact of
      Fact_SpanExc _ tspan v -> case predicate v of
        Just b -> Known (Just b)
        Nothing -> case spanExcJustBefore tspan of
          Nothing -> Known Nothing
          Just t' -> lookupCurrV t' eix predicate allFacts
      Fact_Point _ _ a -> case predicate a of
        Nothing -> lookupPrevV t eix predicate allFacts
        Just b  -> Known (Just b)


-- | Directly lookup the previous value for an event over a span of time.
spanLookupPrevV
  :: TimeSpan
  -- ^ Time or span to lookup
  -> VIx a
  -- ^ Event to lookup
  -> (a -> Maybe b)
  -- ^ predicate / projection.
  -> [SomeValueFact]
  -- ^ All known facts.
  -> ([(TimeSpan, Maybe b)], [TimeSpan])
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
  -> [(TimeSpan, Maybe b)]
  -- ^ All known previous event values (if one exists)
prevVFacts eix predicate allFacts = concat
  [ case fact of
    Fact_SpanExc _ tspan _ -> let
      mayPrevVMay :: MaybeKnown (Maybe b)
      mayPrevVMay = case spanExcJustBefore tspan of
        -- Span starts at -∞ so that's a known Nothing previous event
        Nothing -> Known Nothing
        -- Span starts at a time prevT
        Just prevT -> lookupCurrV prevT eix predicate allFacts
      in case mayPrevVMay of
          Unknown -> []
          Known prevVMay -> (DS_SpanExc tspan, prevVMay) : [(DS_Point nextT, prevVMay) | Just nextT <- [spanExcJustAfter tspan]]
    Fact_Point _ _ _ -> [] -- Point knowledge is handled by the above case
  | fact <- factsV' eix allFacts
  ]

-- | Directly look up all known facts for a given VIx and time or time
-- span.
spanLookupVFacts
  :: TimeSpan
  -- ^ Time or span to lookup
  -> VIx a
  -- ^ Event to lookup
  -> [SomeValueFact]
  -- ^ All known facts.
  -> ([ValueFact a], [TimeSpan])
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

-}