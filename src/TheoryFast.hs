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

module TheoryFast
  ( module TheoryFast
  , module Theory
  ) where

-- import Control.Monad (when)
import Control.Monad.Trans.State.Strict (State, execState, gets, modify)
import Control.Applicative
-- import Data.Hashable
-- import Data.Kind
import Data.List (find)
import qualified Data.IntMap as IM
import           Data.IntMap (IntMap)
import Data.Maybe (fromMaybe, listToMaybe, fromJust)
import qualified Data.Set as S
import Safe
import Unsafe.Coerce
import GHC.Exts (Any)

import Time
import TimeSpan
import Timeline (Timeline)
import qualified Timeline as T

import qualified Theory as Th
import Theory
  ( factTrace
  , VIx(..)
  , SomeVIx(..)

  , ValueM(..)

  , Inputs
  , InputEl(..)

  , MaybeOcc(..)
  , pattern Occ
  , pattern NoOcc

  , MaybeKnown(..)
  , pattern Known
  , pattern Unknown

  , Derivation(..)
  , SomeDerivation(..)
  , startDerivationForAllTime

  , TimeSpan(..)
  , factTSpan

  , DerivationTrace
  , DerivationTraceEl
  , appendDerTrace

  , getV
  , prevV
  , prevVWhere
  )






{-

I'm in the process of changing the KnowledgeBase's representation of Facts from
a map from `VIx a` to `[ValueFact a]` to `Facts` which is a `Timeline`. This
means that the TimeSpan is no longer attached to the fact, but is implied by
it's position in the timeline, so now a "fact" is just `(DerivationTrace a, a)`.
So I've removed ValueFact, now I need to update the usages, and gain some
performance benefits while I do that.

Once this code is compiling again, run the tests. My latest test is a model test
of TheoryFast against Theory. If that passes, then run the Benchmark and append
the git commit hash and benchmark time in PERFORMANCE.md

Then you'll have to continue making this more efficient! The most important
thing is changing the dirty flag in KnowledgeBase from Bool to something similar
to a TimeLine, where we mark the parts of the timeline that are dirty (i.e.
we've learned new facts about). Then we need to store Derivations in a Timeline
like structure too so that we can directly identify the derivations that need to
be continued (based on what is dirty) instead of trying to continue all
derivations in each iteration.




-}





















-- | Facts about a single value.
type ValueTimeline a = Timeline (DerivationTrace a, a)

-- | A bunch of facts about possibly many values.
newtype Facts = Facts (IntMap (ValueTimeline Any))

instance Semigroup Facts where
  (Facts a) <> (Facts b) = Facts $ IM.unionWith (<>) a b

listToFacts :: [Th.SomeValueFact] -> Facts
listToFacts someValueFacts = Facts $ IM.fromListWith (<>)
    [ ( vix
      , T.fromList [(
        factTSpan fact,
        (unsafeCoerce :: (DerivationTrace a, a) -> (DerivationTrace Any, Any)) $
          case fact of
                  Th.Fact_SpanExc derT _ a -> (derT, a)
                  Th.Fact_Point   derT _ a -> (derT, a)
        )]
      )
    | Th.SomeValueFact (VIx vix :: VIx a) fact <- someValueFacts
    ]

singletonFacts :: VIx a -> ValueTimeline a -> Facts
singletonFacts eix tl = Facts $ IM.singleton
  (unVIx eix)
  ((unsafeCoerce :: ValueTimeline a -> ValueTimeline Any) tl)

valueFacts :: VIx a -> Facts -> ValueTimeline a
valueFacts (VIx vix) (Facts vb) = case IM.lookup vix vb of
  Nothing -> T.empty
  Just fs -> (unsafeCoerce :: ValueTimeline Any -> ValueTimeline a) fs

type Derivations = [SomeDerivation]

data KnowledgeBase = KnowledgeBase
  { kbFacts :: Facts
  , kbDerivations :: Derivations
  -- | Is the KnowledgeBase dirty such that some derivations may be able to
  -- progress. This is set to False before attempting to progress all
  -- derivations.
  , kbDirty :: Bool
  }

kbValueFacts :: VIx a -> KnowledgeBase -> ValueTimeline a
kbValueFacts vix kb = valueFacts vix (kbFacts kb)

lookupVKB :: Time -> VIx a -> KnowledgeBase -> MaybeKnown a
lookupVKB t eix kb = lookupV t eix (kbFacts kb)

lookupVKBTrace :: Time -> VIx a -> KnowledgeBase -> MaybeKnown (DerivationTrace a)
lookupVKBTrace t eix kb = lookupVTrace t eix (kbFacts kb)

lookupV :: Time -> VIx a -> Facts -> MaybeKnown a
lookupV t eix facts = snd <$> lookupVFact t eix facts

lookupVTrace :: Time -> VIx a -> Facts -> MaybeKnown (DerivationTrace a)
lookupVTrace t vix facts = fst <$> lookupVFact t vix facts

lookupVFact :: Time -> VIx a -> Facts -> MaybeKnown (DerivationTrace a, a)
lookupVFact t vix facts = MaybeKnown $ do
  let vfs = valueFacts vix facts
  T.lookup t vfs
-- lookupVFact t vix facts = MaybeKnown $ listToMaybe $
--   filter ((`intersects` t) . factTSpan) (valueFacts vix facts)

type KnowledgeBaseM a = State KnowledgeBase a

setClean :: KnowledgeBaseM ()
setClean = modify (\kb -> kb { kbDirty = False })

setDirty :: KnowledgeBaseM ()
setDirty = modify (\kb -> kb { kbDirty = True })

-- Now a natural fist attempt at a solution is obvious: start with an initial
-- knowledge base and continue evaluating derivations until all terminate or
-- deadlock:

solution1 :: Inputs -> KnowledgeBase
solution1 inputs = execState iterateUntilChange initialKb
  where
  initialFacts = listToFacts $ concat
    [ Th.SomeValueFact eix <$> eventFacts
    | InputEl eix (Left eventFacts) <- inputs
    ]
  initialDerivations =
    [ SomeDerivation eix (startDerivationForAllTime eventM)
    | InputEl eix (Right eventM) <- inputs
    ]
  mayProgress = not (null initialDerivations)
  initialKb = KnowledgeBase initialFacts initialDerivations mayProgress

  iterateUntilChange :: KnowledgeBaseM ()
  iterateUntilChange = do
    dirty <- gets kbDirty
    if dirty
      then stepDerivations >> iterateUntilChange
      else return ()

  -- Tries to step all derivations once.
  stepDerivations :: KnowledgeBaseM ()
  stepDerivations = do
    setClean
    n <- gets (length . kbDerivations)
    let loop i = do
          if i == n
            then return ()
            else do
              allDers <- gets kbDerivations
              allFacts <- gets kbFacts
              case allDers !! i of
                SomeDerivation vix der -> do
                  case pokeDerivation vix allDers allFacts der of
                    Nothing -> loop (i + 1)
                    Just (newFacts, newDers) -> do
                      modify (\_ -> KnowledgeBase
                        { kbFacts = (singletonFacts vix newFacts) <> allFacts
                        , kbDerivations = (SomeDerivation vix <$> newDers) <> take i allDers <> drop (i+1) allDers
                        , kbDirty = True
                        })
    loop 0

  -- This is the important part. Is corresponds to the `deriveE` denotation.
  pokeDerivation
    :: forall a
    .  VIx a
    -- ^ Event index that the derivation corresponds to.
    -> [SomeDerivation]
    -- ^ Current derivations. Used to detect PrevV deadlock.
    -> Facts
    -- ^ Current facts. Used to query for existing facts
    -> Derivation a
    -- ^ Derivation to step
    -> Maybe (ValueTimeline a, [Derivation a])
    -- ^ Nothing if no progress. Else Just the new facts and new derivations.
  pokeDerivation eix allDerivations facts derivation = case derivation of
      Derivation dtrace ttspan prevDeps contDerivation -> case contDerivation of
        Pure a -> if null prevDeps
          then Just $ case ttspan of
              DS_Point t -> let
                dtrace' = appendDerTrace dtrace $
                  "Jurisdiction is a point (t=" ++ show t ++ "), ValueM is `Pure a`."
                in (T.singleton (DS_Point t) (dtrace', a), [])

              DS_SpanExc tspanSpan -> let
                dtrace' = appendDerTrace dtrace $
                  "Jurisdiction is (" ++ show tspanSpan ++ "), ValueM is `Pure a`."
                in (T.singleton (DS_SpanExc tspanSpan) (dtrace', a), [])
          else stepCompleteWithPrevDeps a
        GetV eixb cont -> let
          factsBAndUnknownsMay = if null prevDeps
            then Just (spanLookupVFacts ttspan eixb facts)

            -- chronological version of the above with PrevV deps.
            -- TODO this and the above "then" and also the PrevV cases
            -- have very similar code (split on other facts). Try to DRY
            -- it.
            else case T.lookupAtStartOf' ttspan (valueFacts eixb facts) of
              Nothing -> Nothing
              Just (ttspanB, b) -> Just
                ( T.singleton (fromJust $ ttspanB `intersect` ttspan) b
                , ttspan `difference` ttspanB
                )

          in case factsBAndUnknownsMay of
            Nothing -> Nothing
            Just (factsB, unknowns)
              | T.null factsB -> Nothing
              | otherwise -> Just $ (
                -- For knowns, split and try to progress the derivation.
                mconcat
                  [ case ttspanB of
                    DS_SpanExc subTspan -> let
                      newCont = cont valB
                      newDer  = Derivation dtrace (DS_SpanExc subTspan) prevDeps newCont
                                  `withDerTrace`
                                  ("Split on GetV dep (" ++ show eixb ++ ") Fact_SpanExc")
                      in fromMaybe
                        (T.empty, [newDer])
                        -- ^ Couldn't progress further: no new facts, but we've progressed the derivation up to newDer.
                        (pokeDerivation eix allDerivations facts newDer)
                        -- ^ Try to progress further.
                    DS_Point t -> let
                        newCont = cont valB
                        newDer  = Derivation dtrace (DS_Point t) prevDeps newCont
                                  `withDerTrace`
                                  ("Split on GetV dep (" ++ show eixb ++ ") Fact_Point")
                        in fromMaybe
                          (T.empty, [newDer])
                          (pokeDerivation eix allDerivations facts newDer)
                  | (ttspanB, (_, valB)) <- T.elems factsB
                  ]
                <>
                -- For unknowns, simply split the derivation into the
                -- unknown subspans.
                ( T.empty
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
                (T.empty, [newDer])
                (pokeDerivation eix allDerivations facts newDer)
            _ -> undefined

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
                    ( T.empty
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
                _ -> undefined
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
                      (T.empty, [newDer])
                      -- ^ Couldn't progress further: no new facts, but we've progressed the derivation up to newDer.
                      (pokeDerivation eix allDerivations facts newDer)
                      -- ^ Try to progress further.
                  | (ttspan', prevVMay) <- knownSpansAndValueMays
                  ]
                <>
                -- For unknowns, simply split the derivation into the
                -- unknown subspans.
                ( T.empty
                , [ Derivation dtrace subTspan prevDeps contDerivation
                        `withDerTrace`
                          ("Split on unknown span or point")
                  | subTspan <- unknownSpans
                  ]
                )
                )

        where
        -- This is called when a derivation is complete (Pure _ or NoOcc) and
        -- there are some PrevV dependencies.
        stepCompleteWithPrevDeps
          :: a
            -- ^ The derived value (The derivation must have ended with some `Pure a`).
          -> Maybe (ValueTimeline a, [Derivation a])
            -- ^ Taking into account the PrevV deps, if progress can be made,
            -- return the new Facts(s) and any new Derivation(s).
        stepCompleteWithPrevDeps val = case ttspan of

          -- If the ttspan is a point time, then this is easy! Pure x means x.
          DS_Point t -> let
              dtrace' = appendDerTrace dtrace $
                "ValueM is (Pure _). As jurisdiction is a point, we can ignore PrevV deps."
              in Just (T.singleton (DS_Point t) (dtrace', val), [])

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
                  ( T.singleton (DS_SpanExc (spanExc tLoMay ct)) (dtraceF, val)
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
          -- Just (Just t): Fact found that ends at time t (exclusive)
          neighborsAndClearanceByFacts
            :: SomeVIx
            -> Maybe (Maybe Time)
          neighborsAndClearanceByFacts (SomeVIx ix) = findClearanceAfter tLo
            where
            findClearanceAfter :: Maybe Time -> Maybe (Maybe Time)
            findClearanceAfter tMay = case mayFactSpan of
              Just (DS_SpanExc clearanceSpan) -> Just (spanExcJustAfter clearanceSpan)
              Just (DS_Point _) -> error "Implossible!"
              Nothing -> Nothing
              where
              ixFacts = valueFacts ix facts
              mayFactSpan = case tMay of
                Nothing -> fst <$> T.lookupNegInf' ixFacts
                Just t  -> fst <$> T.lookupJustAfter' t ixFacts

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
          in Just (T.empty, [newDer])

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
          in Just (T.empty, newDers)

        -- There is no first occ, so this derivation covers no time, so
        -- we stop.
        NoChangeInSpan -> Just (T.empty, [])

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
  -> Facts
  -- ^ All known facts.
  -> FirstValueChange
searchForFirstChange tspan vix allFacts = let
  -- TODO I think this could be simplified by pattern matching on facts with
  -- some guards.
  facts = T.elems $ T.cropTimeSpan (DS_SpanExc tspan) (valueFacts vix allFacts)
  firstKnownTChangeMay     = headMay [ t      | (DS_Point   t     , _) <- facts]
  firstKnownTSpanChangeMay = headMay [ tspan' | (DS_SpanExc tspan', _) <- facts]
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
  -> Facts
  -- ^ Known facts.
  -> MaybeKnown (Maybe b)
  -- ^ Unknown: if unknown
  -- Known Nothing: if no value satisfying the predicate occurs strictly before t.
  -- Known (Just b): the latest (projected) value satisfying the predicate (strictly before time t).
lookupPrevV t eix predicate allFacts = MaybeKnown $ case T.lookupJustBefore' t (valueFacts eix allFacts) of
  Nothing -> Nothing
  Just (ttspan, (_, a)) -> case ttspan of
    DS_Point _ -> error "Impossible! lookupJustBefore' can't return a point"
    DS_SpanExc tspan -> case predicate a of
      Just b -> Just (Just b)
      Nothing -> case spanExcJustBefore tspan of
                Nothing -> Just Nothing
                Just tLo -> maybeKnownToMaybe $ lookupCurrV tLo eix predicate allFacts


  -- factSpanExcs = mapMaybe factSpa
  --     (\case
  --       Fact_Point _ _ _ -> Nothing
  --       Fact_SpanExc _ tspan _ -> Just tspan
  --     )
  --     (valueFacts eix allFacts)
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
  -> Facts
  -- ^ Known facts.
  -> MaybeKnown (Maybe b)
  -- ^ Unknown: if unknown
  -- Known Nothing: if no value satisfying the predicate occurs at or before t.
  -- Known (Just b): the latest (projected) value satisfying the predicate (at or before t).
lookupCurrV tTop eix predicate allFacts = go tTop
  where
  facts = valueFacts eix allFacts
  go t = case T.lookup' t facts of
    Nothing -> Unknown
    Just (ttspan', (_, a)) -> case predicate a of
      Nothing -> case ttspan' of
        DS_Point t' -> lookupPrevV t' eix predicate allFacts
        DS_SpanExc tspan' -> case spanExcJustBefore tspan' of
          Nothing -> Known Nothing
          Just t' -> go t'
      Just b -> Known (Just b)


-- | Directly lookup the previous value for an event over a span of time.
spanLookupPrevV
  :: TimeSpan
  -- ^ Time or span to lookup
  -> VIx a
  -- ^ Event to lookup
  -> (a -> Maybe b)
  -- ^ predicate / projection.
  -> Facts
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
  -> Facts
  -- ^ All known facts.
  -> [(TimeSpan, Maybe b)]
  -- ^ All known previous event values (if one exists)
prevVFacts eix predicate allFacts = concat
  [ case ttspan of
    DS_SpanExc tspan -> let
      mayPrevVMay :: MaybeKnown (Maybe b)
      mayPrevVMay = case spanExcJustBefore tspan of
        -- Span starts at -∞ so that's a known Nothing previous event
        Nothing -> Known Nothing
        -- Span starts at a time prevT
        Just prevT -> lookupCurrV prevT eix predicate allFacts
      in case mayPrevVMay of
          Unknown -> []
          Known prevVMay -> (DS_SpanExc tspan, prevVMay) : [(DS_Point nextT, prevVMay) | Just nextT <- [spanExcJustAfter tspan]]
          _ -> undefined
    DS_Point _ -> [] -- Point knowledge is handled by the above case
  | (ttspan, _) <- T.elems (valueFacts eix allFacts)
  ]

-- | Directly look up all known facts for a given VIx and time or time
-- span.
spanLookupVFacts
  :: TimeSpan
  -- ^ Time or span to lookup
  -> VIx a
  -- ^ Event to lookup
  -> Facts
  -- ^ All known facts.
  -> (ValueTimeline a, [TimeSpan])
  -- ^ ( Facts about the given VIx
  --   , unknown times and time spans )
  --   The union of these facts and times and time spans should exactly
  --   equal the input time/time span.
spanLookupVFacts tspan eix allFacts = let
  knownFacts = T.cropTimeSpan tspan (valueFacts eix allFacts)
  knownTSpans = fst <$> T.elems knownFacts
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
