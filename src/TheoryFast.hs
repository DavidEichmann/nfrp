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
import Control.Monad.Trans.RWS.CPS (asks, RWS, runRWS, tell)
-- import Data.Hashable
-- import Data.Kind
import Data.List (find)
import qualified Data.Map as M
import           Data.Map (Map)
import qualified Data.IntMap as IM
import           Data.IntMap (IntMap)
import Data.Maybe (fromJust)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Coerce (coerce)
import Unsafe.Coerce
import GHC.Exts (Any)
import Safe (minimumMay)

import DMap (DMap)
import qualified DMap as DM
import MultiTimeline (MultiTimeline)
import qualified MultiTimeline as MT
import Time
import TimeSpan
import Timeline (Timeline)
import qualified Timeline as T

import qualified Theory as Th
import Theory
  ( factTrace
  , EIx(..)
  , SomeEIx(..)

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

  , getE
  , prevV
  )
-- import Control.Monad (when)
import Data.List (foldl')


-- | Facts about a single value.
type ValueTimeline a = Timeline (DerivationTrace a) a
newtype ValueTimelineW a = ValueTimeline { unVTW :: ValueTimeline a }
  deriving newtype (Semigroup)

-- | A bunch of facts about possibly many values.
type Facts = DMap EIx ValueTimelineW

listToFacts :: [Th.SomeValueFact] -> Facts
listToFacts someValueFacts = DM.fromListWith (<>)
    [ DM.El
        eix
        (ValueTimeline $ case fact of
          Th.Fact_NoOcc derT tts -> T.singletonNoOcc derT tts
          Th.Fact_Occ   derT t a -> T.singletonOcc derT t a
        )
    | Th.SomeValueFact eix fact <- someValueFacts
    ]

singletonFacts :: EIx a -> ValueTimeline a -> Facts
singletonFacts eix vt = DM.singleton eix  (ValueTimeline vt)

valueFacts :: EIx a -> Facts -> ValueTimeline a
valueFacts eix facts = maybe T.empty unVTW (DM.lookup eix facts)

data KnowledgeBase = KnowledgeBase
  { kbFacts :: Facts


  -- , kbDerivations :: Derivations
  -- -- | Is the KnowledgeBase dirty such that some derivations may be able to
  -- -- progress. This is set to False before attempting to progress all
  -- -- derivations.
  -- , kbDirty :: Bool


  -- WIP derivation tracking by deps
  , kbDerivations :: DerivationsByDeps
  , kbHotDerivations :: Set SomeDerivationID
  }

kbValueFacts :: EIx a -> KnowledgeBase -> ValueTimeline a
kbValueFacts vix kb = valueFacts vix (kbFacts kb)

lookupVKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
lookupVKB t eix kb = lookupV t eix (kbFacts kb)

lookupVKBTrace :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (DerivationTrace a)
lookupVKBTrace t eix kb = lookupVTrace t eix (kbFacts kb)

lookupV :: Time -> EIx a -> Facts -> MaybeKnown (MaybeOcc a)
lookupV t eix facts = snd <$> lookupVFact t eix facts

lookupVTrace :: Time -> EIx a -> Facts -> MaybeKnown (DerivationTrace a)
lookupVTrace t vix facts = fst <$> lookupVFact t vix facts

lookupVFact :: Time -> EIx a -> Facts -> MaybeKnown (DerivationTrace a, MaybeOcc a)
lookupVFact t vix facts = MaybeKnown $ do
  let vfs = valueFacts vix facts
  (tr, eitherNoOccSpanOrOcc) <- T.lookup' t vfs
  return (tr, either (const NoOcc) id eitherNoOccSpanOrOcc)

type KnowledgeBaseM a = State KnowledgeBase a

-- Some data to store/query derivations according to their dependencies
data DerivationsByDeps = DerivationsByDeps
  { dbdNextID :: Int
  , dbdDerivation :: IntMap (DbdDerivation_Value Any) -- Map (DerivationID a) (EIx a, Derivation a)

  -- Derivations keyed on dependencies

  -- Ixs to DerivationIDs
  -- TODO and indexes, then update:
  --  * dbdDelete
  --  * dbdSetDeps
  --  * ???

  , dbdIxSpanLoJurisdiction :: Map (SomeEIx, Maybe Time) Int -- Map (EIx a, Maybe Time) DerivationID
  -- ^ Used for `dbdLookupSpanDerJustAfter`. Key is lo time of derivation
  -- jurisdiction. Only applies to (non-DeriveAfterFirstChange) derivations with
  -- a span jurisdiction. Nothing means (-Inf).

  , dbdIxDependantByEIxSpan :: Map SomeEIx (MultiTimeline SomeDerivationID)
  -- ^ (dbdIxDependantByEIxSpan ! eix) `MT.select` span = derivations that depend on eix at span.
  -- Used for: Dep_FactSpan TimeSpan (EIx a)

  }

type DbdDerivation_Value a = (EIx a, Derivation a)

-- | Get the key in to dbdIxSpanLoJurisdiction
dbdIxKeySpanLoJurisdiction :: EIx a -> Derivation a -> Maybe (SomeEIx, Maybe Time)
dbdIxKeySpanLoJurisdiction vix der = case der of
  Derivation _ (DS_SpanExc tspan) _ _ _ -> Just (SomeEIx vix, spanExcJustBefore tspan)
  _ -> Nothing


newtype DerivationID a = DerivationID Int
  deriving (Eq, Ord)
data SomeDerivationID = forall a . SomeDerivationID (EIx a) (DerivationID a)
instance Eq SomeDerivationID where
  (SomeDerivationID vixA derIdA) == (SomeDerivationID vixB derIdB)
    = vixA == coerce vixB && derIdA == coerce derIdB
instance Ord SomeDerivationID where
  compare (SomeDerivationID vixA derIdA) (SomeDerivationID vixB derIdB)
    = compare (vixA, derIdA) (coerce (vixB, derIdB))

dbdLookupDer :: DerivationID a -> DerivationsByDeps -> Maybe (EIx a, Derivation a)
dbdLookupDer (DerivationID derIdInt) dbd = fmap
  (unsafeCoerce :: DbdDerivation_Value Any -> DbdDerivation_Value a)
  (IM.lookup derIdInt (dbdDerivation dbd))

-- | Lookup a derivation that spans just after the given time.
dbdLookupSpanDerJustAfter
  :: EIx a
  -> Maybe Time
  -- ^ Nothing means -Inf
  -> DerivationsByDeps
  -> Maybe (DerivationID a, Derivation a)
dbdLookupSpanDerJustAfter vix t dbd = do
  let ix = dbdIxSpanLoJurisdiction dbd
  derId <- M.lookup (SomeEIx vix, t) ix
  let (_, der) = (unsafeCoerce :: DbdDerivation_Value Any -> DbdDerivation_Value a)
        (dbdDerivation dbd IM.! derId)
  return (DerivationID derId, der)

dbdInitialEmpty :: DerivationsByDeps
dbdInitialEmpty = DerivationsByDeps
  { dbdNextID = 0
  , dbdDerivation = IM.empty
  , dbdIxSpanLoJurisdiction = M.empty
  }

dbdInitialFromListNoDeps :: [SomeDerivation] -> ([SomeDerivationID], DerivationsByDeps)
dbdInitialFromListNoDeps ders = dbdInsertsNoDeps ders dbdInitialEmpty

dbdInsertsNoDeps :: [SomeDerivation] -> DerivationsByDeps -> ([SomeDerivationID], DerivationsByDeps)
dbdInsertsNoDeps someDers dbd = (reverse revIds, dbdFinal)
  where
  (revIds, dbdFinal) = foldl'
      (\(ids, dbd') (SomeDerivation vix der) ->
        let (newId, dbd'') = dbdInsertNoDeps vix der dbd'
        in (SomeDerivationID vix newId : ids, dbd'')
      )
      ([], dbd)
      someDers

dbdInsertNoDeps :: EIx a -> Derivation a -> DerivationsByDeps -> (DerivationID a, DerivationsByDeps)
dbdInsertNoDeps vix der dbd =
  ( myId
  , DerivationsByDeps
    { dbdNextID = dbdNextID dbd + 1
    , dbdDerivation = IM.insert
        myIdInt
        ((unsafeCoerce :: DbdDerivation_Value a -> DbdDerivation_Value Any) (vix, der))
        (dbdDerivation dbd)
    , dbdIxSpanLoJurisdiction = case dbdIxKeySpanLoJurisdiction vix der of
        Just key -> M.insert key myIdInt (dbdIxSpanLoJurisdiction dbd)
        Nothing -> dbdIxSpanLoJurisdiction dbd
    }
  )
  where
  myIdInt = dbdNextID dbd
  myId = DerivationID myIdInt

dbdDelete :: DerivationID a -> DerivationsByDeps -> DerivationsByDeps
dbdDelete (DerivationID derIdInt) dbd = case IM.lookup derIdInt (dbdDerivation dbd) of
  Nothing -> dbd
  Just (vix, der) -> DerivationsByDeps
    { dbdNextID = dbdNextID dbd
    , dbdDerivation = IM.delete derIdInt (dbdDerivation dbd)
    , dbdIxSpanLoJurisdiction = case dbdIxKeySpanLoJurisdiction vix der of
        Nothing -> dbdIxSpanLoJurisdiction dbd
        Just key -> M.delete key (dbdIxSpanLoJurisdiction dbd)
    }

dbdSetDeps :: DerivationID a -> [DerivationDep] -> DerivationsByDeps -> DerivationsByDeps
dbdSetDeps _derID _deps dbd = dbd

-- | Which derivations are affected (dependencies may have changed) given new
-- facts and derivations.
dbdAffectedDers
  :: [SomeDerivation]
  -- ^ New derivations. This is needed as it may affect Derivation based
  -- clearances.
  -> Facts
  -- ^ New facts.
  -> DerivationsByDeps
  -- ^ Existing derivations.
  -> Set SomeDerivationID
  -- ^ Affected existing derivations.
dbdAffectedDers newDers newFacts derByDeps = S.fromList . concat
  -- Dep_FactSpan
  $ [ MT.elems
      $ MT.select newFactSpan
      $ dbdIxDependantByEIxSpan derByDeps M.! SomeEIx newFactEIx

    | DM.SomeIx newFactEIx <- DM.keys newFacts
    , (_, eitherNoOccSpanOrOcc) <- T.elems (valueFacts newFactEIx newFacts)
    , let newFactSpan = case eitherNoOccSpanOrOcc of
            Left tspan -> timeSpanToSpan tspan
            Right (t, _) -> timeToSpan t
    ]
  -- TODO Dep_NegInf
  -- TODO Dep_JustBefore
  -- TODO Dep_JustAfter
  -- TODO Dep_DerivationClearance


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
  (initialDerivationIDs, initialDerivations) = dbdInitialFromListNoDeps
    [ SomeDerivation eix (startDerivationForAllTime eventM)
    | InputEl eix (Right eventM) <- inputs
    ]
  initialKb = KnowledgeBase
                { kbFacts = initialFacts
                , kbDerivations = initialDerivations
                , kbHotDerivations = S.fromList initialDerivationIDs
                }

  iterateUntilChange :: KnowledgeBaseM ()
  iterateUntilChange = go
    where
      -- Try remove a derivation from kbHotDerivations
      popHotDerivation = do
        mvMay <- gets (S.minView . kbHotDerivations)
        case mvMay of
          Nothing -> return Nothing
          Just (derId, newHotDers) -> do
            modify (\kb -> kb { kbHotDerivations = newHotDers })
            return (Just derId)

      go = do
        -- Pop a DerivatiopnID off the Hot list
        derIdMay <- popHotDerivation
        case derIdMay of
          Nothing -> return ()
          Just (SomeDerivationID vix derId) -> do
            -- Poke the Derivation
            derMay <- gets (dbdLookupDer derId . kbDerivations)
            let Just (_, der) = derMay
            allDers <- gets kbDerivations
            allFacts <- gets kbFacts
            let (mayNewFactsAndDers, (), deps) = runRWS (pokeDerivation vix der) (allFacts, allDers) ()
            case mayNewFactsAndDers of
              -- If no progress, simply update the deps (they may have changed).
              Nothing -> modify (\kb -> kb { kbDerivations = dbdSetDeps derId deps (kbDerivations kb) })
              -- Else we made progress and should add the new facts and (hot) derivations.
              Just (newFactsTl, newDers) -> do
                oldHotDers <- gets kbHotDerivations -- note we've already popped off derId
                let newSomeDers = SomeDerivation vix <$> newDers
                    newFacts = singletonFacts vix newFactsTl
                    (newDerIds, newKbDers)
                      = dbdInsertsNoDeps newSomeDers
                      $ dbdDelete derId allDers
                    newKbHotDers
                      = oldHotDers
                      -- New derivations are all hot (we haven't calculated their deps yet)
                      <> S.fromList newDerIds
                      -- As dependencies have changed, more Derivations may be hot.
                      <> dbdAffectedDers newSomeDers newFacts
                modify (\kb -> KnowledgeBase
                  { kbFacts = kbFacts kb <> newFacts
                  , kbDerivations = newKbDers
                  , kbHotDerivations = newKbHotDers
                  })
            go

  -- This is the important part. Is corresponds to the `deriveE` denotation.
  pokeDerivation
    :: forall a
    .  EIx a
    -- ^ Event index that the derivation corresponds to.

    -- TODO all this will be moved to the monad's state.
    -- -> [SomeDerivation]
    -- -- ^ Current derivations. Used to detect PrevV deadlock. May include the
    -- -- derivation we are stepping.
    -- -> Facts
    -- -- ^ Current facts. Used to query for existing facts

    -> Derivation a
    -- ^ Derivation to step
    -> DerivationM (Maybe (ValueTimeline a, [Derivation a]))
    -- ^ Nothing if no progress. Else Just the new facts and new derivations.
  pokeDerivation eix derivation = case derivation of
      Derivation dtrace ttspan prevDeps contDerivation seenOcc -> case contDerivation of
        Pure NoOcc -> if null prevDeps
          then let
                dtrace' = appendDerTrace dtrace $
                  "Pure NoOcc (t=" ++ show ttspan ++ ")."
                in return $ Just (T.singletonNoOcc dtrace' ttspan, [])
          else stepCompleteNoOccWithPrevDeps
        Pure (Occ a) -> return $ case ttspan of
          DS_SpanExc _ -> error "Pure (Occ _) when jurisdiction is not a point"
          DS_Point t -> let
                  dtrace' = appendDerTrace dtrace $
                    "Jurisdiction is a point (t=" ++ show t ++ "), ValueM is `Pure a`."
                  in Just (T.singletonOcc dtrace' t a, [])

        GetE eixb cont -> do
          factsBAndUnknownsMay <- if null prevDeps
                then Just <$> spanLookupVFacts ttspan eixb

                -- chronological version of the above with PrevV deps.
                -- TODO this and the above "then" and also the PrevV cases
                -- have very similar code (split on other facts). Try to DRY
                -- it.
                else do
                  valMay <- lookupAtStartOf' ttspan eixb
                  pure $ case valMay of
                    Nothing -> Nothing
                    Just (tr, Left ttspanB) -> Just
                      ( T.singletonNoOcc tr (fromJust $ ttspanB `intersect` ttspan)
                      , ttspan `difference` ttspanB
                      )
                    -- ttspan is a point
                    Just (tr, Right (t, occMay)) -> Just
                      ( case occMay of
                          NoOcc -> T.singletonNoOcc tr ttspan
                          Occ a -> T.singletonOcc tr t a
                      , ttspan `difference` t
                      )

          pure $ case factsBAndUnknownsMay of
            Nothing -> Nothing
            Just (factsB, unknowns)
              | T.null factsB -> Nothing
              | otherwise -> Just $ (
                -- For knowns, split and try to progress the derivation.
                mconcat
                  [ case fact of
                    -- NoOcc
                    Left factTspan -> let
                      newCont = cont NoOcc
                      newDer  = Derivation dtrace factTspan prevDeps newCont seenOcc
                                  `withDerTrace`
                                  ("Split on GetE dep (" ++ show eixb ++ ") Fact_SpanExc")
                      in (T.empty, [newDer])

                    -- Occ
                    Right (factT, b) -> let
                      newCont = cont (Occ b)
                      newDer  = Derivation dtrace (DS_Point factT) prevDeps newCont True
                                `withDerTrace`
                                ("Split on GetE dep (" ++ show eixb ++ ") Fact_Point")
                      in (T.empty, [newDer])
                  | (_, fact) <- T.elems factsB
                  ]
                <>
                -- For unknowns, simply split the derivation into the
                -- unknown subspans.
                ( T.empty
                , [ Derivation dtrace subTspan prevDeps contDerivation seenOcc
                    `withDerTrace`
                    ("Split on GetE dep (" ++ show eixb ++ ") unknown point or span.")
                  | subTspan <- unknowns
                  ]
                )
              )

        PrevV eixB mayPrevToCont -> case ttspan of
          DS_Point t -> do
            mayPrevVB <- lookupPrevV t eixB
            pure $ case mayPrevVB of
              Unknown -> Nothing
              Known prevBMay -> Just $ let
                newCont = mayPrevToCont prevBMay
                newDer  = Derivation dtrace ttspan (SomeEIx eixB : prevDeps) newCont seenOcc
                      `withDerTrace`
                      ("Use known PrevV value of dep (" ++ show eixB ++ ")")
                in (T.empty, [newDer])
              _ -> undefined

          -- !! The Plan
          -- !! Try and split on facts about eixB.
          DS_SpanExc tspan -> do
            prevVSpans <- spanLookupPrevV ttspan eixB
            let -- | Nothing means tried chronological order, but found no fact.
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
            let tryChonologicalSplit = do
                  let tspanLo = spanExcJustBefore tspan
                  prevValMayIfKnown <- case tspanLo of
                        Nothing -> pure (Known Nothing) -- Known: there is no previous value.
                        Just tLo -> lookupCurrV tLo eixB
                  return $ case prevValMayIfKnown of
                    Unknown -> Nothing
                    Known prevValMay -> Just
                      ( T.empty
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
                    _ -> undefined
            case factsAndUnknownsMay of
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
              Just (knownSpansAndValueMays, unknownSpans) -> return $ Just $ (
                -- For knowns, split and try to progress the derivation.
                mconcat
                  [ let
                    newCont = mayPrevToCont prevVMay
                    newDer  = Derivation dtrace ttspan' prevDeps newCont seenOcc
                        `withDerTrace`
                          ("Split on known facts")
                    in (T.empty, [newDer])
                  | (ttspan', prevVMay) <- knownSpansAndValueMays
                  ]
                <>
                -- For unknowns, simply split the derivation into the
                -- unknown subspans.
                ( T.empty
                , [ Derivation dtrace subTspan prevDeps contDerivation seenOcc
                        `withDerTrace`
                          ("Split on unknown span or point")
                  | subTspan <- unknownSpans
                  ]
                )
                )
        where
        -- This is called when a derivation is complete (Pure NoOcc) and
        -- there are some PrevV dependencies.
        stepCompleteNoOccWithPrevDeps
          :: DerivationM (Maybe (ValueTimeline a, [Derivation a]))
          -- ^ Taking into account the PrevV deps, if progress can be made,
          -- return the new Fact(s) and any new Derivation(s)
        stepCompleteNoOccWithPrevDeps = case ttspan of

          -- If the ttspan is a point time, then this is easy! Pure NoOcc means NoOcc.
          DS_Point _ -> let
              dtrace' = appendDerTrace dtrace $
                "ValueM is (Pure NoOcc). As jurisdiction is a point, we can ignore PrevV deps."
              in return $ Just (T.singletonNoOcc dtrace' ttspan, [])

          -- If the ttspan is a span, things get more tricky. At this point we
          -- need to find a "clearance time". This is some time span at the
          -- start of ttspan where whe know none of the PrevV deps are changing
          -- (within the time jurisdiction of this Derivation). We do this by
          -- finding the transitive closure of PrevV dependencies. For each dep
          -- we have either facts indicating for how long no there is no change,
          -- or a complete derivation, or an incomplete derivation.
          DS_SpanExc tspan -> do
            let tLoMay = spanExcJustBefore tspan
            -- Clearance time iff after the start of tspan. Note that the
            -- clearance time must be in tspan or at the time just after tspan.
            -- This is a natural consequence of the fact that we observe the
            -- current Derivation as part of the calculation of clearance time.
            ctMay <- clearanceTime (SomeEIx eix) tLoMay
            return $ case ctMay of
              -- We don't know the clearance time, so return Nothing.
              Nothing -> Nothing
              Just ct ->  let
                msgCt = "Found clearance time ct=" ++ show ct ++ "."
                dtraceF = appendDerTrace dtrace $
                  msgCt ++ " This means no value changes are occuring up to at least that time."
                in Just
                  ( T.singletonNoOcc dtraceF (DS_SpanExc (spanExc tLoMay ct))
                  -- If ct is not Inf (i.e. Nothing) and is within the current
                  -- jurisdiction (i.e. tspan), then we need to cover the
                  -- clearance time at and after ct.
                  , case ct of
                      Just ctPoint | tspan `contains` ctPoint
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
          -> DerivationM (Maybe (Maybe Time))
                          -- ^ Clearance time if greater than the input time ((exclusive) end of the span of NoOcc). Just Nothing means Inf.
        clearanceTime ix' tLo = do
          -- Get the initial "local" clearance.
          -- local clearance is the clearance assuming that prevV dependencies never change.
          -- The clearance is min{local clearance, clearance of dependencies}
          ncMay <- neighborsAndClearance ix'
          case ncMay of
            Nothing -> return Nothing
            Just (neighbors, ixClearanceTime)
              -> go
                  neighbors
                  (S.singleton ix')
                  ixClearanceTime
          where
          go
            :: [SomeEIx]
              -- ^ Stack of `EIx`s to visit
            -> S.Set SomeEIx
              -- ^ visited `EIx`s
            -> Maybe Time
              -- ^ clearance time so far (if any).
            -> DerivationM (Maybe (Maybe Time))
              -- ^ clearance time if greater than input time.
          go [] _ clearance = pure (Just clearance)
          go (ix:ixs) visited clearance
            | ix `S.member` visited = go ixs visited clearance
            | otherwise = do
                ncMay <- neighborsAndClearance ix
                case ncMay of
                  Just (neighbors, ixClearanceTime)
                    -> go
                        (neighbors++ixs)
                        (S.insert ix visited)
                        (minClearance ixClearanceTime clearance)
                  Nothing -> return Nothing

          -- | For clearance time, Nothing means Inf so account for that here.
          minClearance :: Maybe Time -> Maybe Time -> Maybe Time
          minClearance Nothing a = a
          minClearance a Nothing = a
          minClearance (Just a) (Just b) = Just (min a b)

          -- | Get the neighbors (PrevV deps) and local clearance time of a
          -- single EIx.
          neighborsAndClearance
            :: SomeEIx
            -> DerivationM (Maybe ([SomeEIx], Maybe Time))
          neighborsAndClearance ix = do
            clearanceByFactsMay <- neighborsAndClearanceByFacts ix
            case clearanceByFactsMay of
              Just clearance -> pure $ Just ([], clearance)
              Nothing -> neighborsAndClearanceByDerivation ix

          -- | Get the clearance time (ignoring neighbors) of a single value
          -- by looking for a fact spanning the time just after tLo.
          --
          -- Nothing: No fact spanning the time.
          -- Just Nothing: Fact found that goes to infinity
          -- Just (Just t): Fact found that ends at time t (exclusive)
          neighborsAndClearanceByFacts
            :: SomeEIx
            -> DerivationM (Maybe (Maybe Time))
          neighborsAndClearanceByFacts (SomeEIx ix) = findClearanceAfter tLo
            where
            findClearanceAfter :: Maybe Time -> DerivationM (Maybe (Maybe Time))
            findClearanceAfter tMay = do
              mayFactSpan <- fmap snd <$> case tMay of
                Nothing -> lookupNegInf' ix
                Just t  -> lookupJustAfter' t ix
              return $ case mayFactSpan of
                Just clearanceSpan -> Just (spanExcJustAfter clearanceSpan)
                Nothing -> Nothing

          -- | Get the neighbors (PrevV deps) and local clearance time of a
          -- single EIx. Only considers active Derivations, not facts.
          neighborsAndClearanceByDerivation
            :: SomeEIx
            -> DerivationM (Maybe ([SomeEIx], Maybe Time))
          neighborsAndClearanceByDerivation (SomeEIx depIx) = do
            tellDep (Dep_DerivationClearance tLo depIx)
            derMay <- dbdLookupSpanDerJustAfter depIx tLo <$> untrackedAskDerivations
            return $ case derMay of
              Just ( _
                   , Derivation
                        _
                        (DS_SpanExc tspan) -- Must be of this form due to `dbdLookupSpanDerJustAfter`
                        neighbors
                        (Pure _)
                        _
                   )
                   -> Just (neighbors, spanExcJustAfter tspan)
              _ -> Nothing

      DeriveAfterFirstChange dtrace tspan eixB cont -> do
       fc <- searchForFirstChange tspan eixB
       return $ case fc of
        -- We know the time of the first occurrence, so we can convert
        -- to a concrete time span again.
        FirstChangeIsAt firstChangeTime -> let
          -- Safe to use mono-bind here as firstChangeTime ∈ tspan
          Just concreteTimeSpan = tspan `intersect` RightSpaceExc firstChangeTime
          newDer = Derivation
            dtrace
            (DS_SpanExc concreteTimeSpan)
            -- NOTE [DeriveAfterFirstChange and PrevV deps] There are
            -- no PrevV events by denotation of DeriveAfterFirstChange
            []
            cont
            False -- We're in a span jurisdiction and haven't witnessed an event.
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
  -> EIx a
  -- ^ Event to lookup
  -> DerivationM FirstValueChange
searchForFirstChange tspan vix = do
  (factsTl, unknownDSpans) <- spanLookupVFacts (DS_SpanExc tspan) vix
  let facts = T.elems factsTl
      firstKnownTChangeMay = minimumMay [ t | (_, Right (t, _))  <- facts]
  return $ case firstKnownTChangeMay of
      -- No known event occurrence
      Nothing -> if null unknownDSpans
        -- And we have full knowlage.
        then NoChangeInSpan
        -- but there is missing knowledge. TODO we could have
        -- FirstChangeIsAtOrBefore by observing a span of NoOcc at the end of
        -- tspan. I'm not sure if that's necessary or not.
        else Other
      -- There is some known first occurrence
      Just t
        -- It is the true first occurrence.
        | any (intersects (fromJust $ tspan `intersect` (LeftSpaceExc t))) unknownDSpans -> FirstChangeIsAtOrBefore t
        -- It may not be the the true first occurrence.
        | otherwise -> FirstChangeIsAt t

-- | Directly look up the previous value that satisfies the predicate
-- (strictly before the given time).
lookupPrevV
  :: Time
  -- ^ Time t
  -> EIx a
  -- ^ Event to lookup.
  -> DerivationM (MaybeKnown (Maybe a))
  -- ^ Unknown: if unknown
  -- Known Nothing: if no event occurs strictly before t.
  -- Known (Just a): the latest event value (strictly before time t).
lookupPrevV t vix = do
  vMay <- lookupJustBefore' t vix
  case vMay of
    Nothing -> return Unknown
    Just (_, tspan) -> case spanExcJustBefore tspan of
      Nothing -> return $ Known Nothing
      Just tLo -> lookupCurrV tLo vix

-- | Directly look up the current (i.e. latest) event occurrence (equal or before the given time).
lookupCurrV
  :: Time
  -- ^ Time t
  -> EIx a
  -- ^ Event to lookup.
  -> DerivationM (MaybeKnown (Maybe a))
  -- ^ Unknown: if unknown
  -- Known Nothing: if no event occurs at or before t.
  -- Known (Just a): the latest event value (at or before time t).
lookupCurrV t eix = do
  aMay <- lookupM' t eix
  case aMay of
    Nothing -> return Unknown
    Just (_, (Left tspan)) -> case spanExcJustBefore tspan of
      Nothing -> return (Known Nothing)
      Just t' -> lookupCurrV t' eix
    Just (_, (Right NoOcc)) -> lookupPrevV t eix
    Just (_, (Right (Occ a))) -> return (Known (Just a))

-- | Directly lookup the previous value for an event over a span of time.
spanLookupPrevV
  :: TimeSpan
  -- ^ Time or span to lookup
  -> EIx a
  -- ^ Event to lookup
  -> DerivationM ([(TimeSpan, Maybe a)], [TimeSpan])
  -- ^ ( Known values about the given EIx
  --   , unknown times and time spans )
  --   The union of these times and time spans should exactly
  --   equal the input time/time span.
spanLookupPrevV tspan eix = do
  facts <- prevVFacts tspan eix
  let knownFacts =
          [ (ttspan', aMay)
          | (factTspan, aMay) <- facts
          , Just ttspan' <- [factTspan `intersect` tspan]
          ]
      knownTSpans = fst <$> knownFacts
      unknownTSpans = tspan `difference` knownTSpans
  return (knownFacts, unknownTSpans)


-- | Get all known PervV spans for an event cropped to the given time span.
prevVFacts
  :: forall a
  .  TimeSpan
  -- ^ Time or span to lookup
  -> EIx a
  -- ^ Event to lookup
  -> DerivationM [(TimeSpan, Maybe a)]
  -- ^ All known previous event values (if one exists)
prevVFacts timeSpan vix = do
  (factsTl, _) <- spanLookupVFacts timeSpan vix
  fs' <- sequence
    [ case fact of
      Left (DS_SpanExc tspan) -> do
        mayPrevVMay <- case spanExcJustBefore tspan of
          -- Span starts at -∞ so that's a known Nothing previous event
          Nothing -> pure (Known Nothing)
          -- Span starts at a time prevT
          Just prevT -> lookupCurrV prevT vix
        return $ case mayPrevVMay of
            Unknown -> []
            Known prevVMay -> (DS_SpanExc tspan, prevVMay) : [(DS_Point nextT, prevVMay) | Just nextT <- [spanExcJustAfter tspan]]
            _ -> undefined

      -- Point knowledge is handled by the above case
      Left (DS_Point _) -> pure []
      Right _ -> pure []

    | (_, fact) <- T.elems factsTl
    ]
  return $ concat fs'
-- prevVFacts eix predicate allFacts = concat
--   [ case ttspan of
--     DS_SpanExc tspan -> let
--       mayPrevVMay :: MaybeKnown (Maybe b)
--       mayPrevVMay = case spanExcJustBefore tspan of
--         -- Span starts at -∞ so that's a known Nothing previous event
--         Nothing -> Known Nothing
--         -- Span starts at a time prevT
--         Just prevT -> lookupCurrV prevT eix predicate allFacts
--       in case mayPrevVMay of
--           Unknown -> []
--           Known prevVMay -> (DS_SpanExc tspan, prevVMay) : [(DS_Point nextT, prevVMay) | Just nextT <- [spanExcJustAfter tspan]]
--           _ -> undefined
--     DS_Point _ -> [] -- Point knowledge is handled by the above case
--   | (ttspan, _) <- T.elems (valueFacts eix allFacts)
--   ]


--
-- DerivationM a monad that tracks dependencies used while stepping a derivation.
--

type DerivationM a = RWS (Facts, DerivationsByDeps) [DerivationDep] () a

tellDep :: DerivationDep -> DerivationM ()
tellDep dep = tell [dep]

-- Use `tellDeps` after this to track what part of facts you depend on.
untrackedAskFacts :: DerivationM Facts
untrackedAskFacts = asks fst

-- Use `tellDeps` after this to track what part of derivations you depend on.
untrackedAskDerivations :: DerivationM DerivationsByDeps
untrackedAskDerivations = asks snd

-- Describes a dependency
data DerivationDep
  -- Depend on all facts in a time span for a Vix
  = forall a . Dep_FactSpan TimeSpan (EIx a)
  -- Depend on all the value at -Inf a Vix
  | forall a . Dep_NegInf (EIx a)
  -- Depend on all the value just after t of a Vix
  | forall a . Dep_JustBefore Time (EIx a)
  -- Depend on all the value just before t of a Vix
  | forall a . Dep_JustAfter Time (EIx a)
  -- Depend on the derivation based clearance of a Vix just after a given time.
  -- That's a completed (continuation is Pure _) Derivation spanning a time just
  -- after the given time. (Nothing means -Inf)
  | forall a . Dep_DerivationClearance (Maybe Time) (EIx a)

--
-- DerivationM Primitives
--

-- | Directly look up all known facts for a given EIx and time or time span.
--
-- TODO This causes a dep on the whole span, but at the use sights we may be
-- using less info.
spanLookupVFacts
  :: TimeSpan
  -- ^ Time or span to lookup
  -> EIx a
  -- ^ Event to lookup
  -- ^ All known facts.
  -> DerivationM (ValueTimeline a, [TimeSpan])
  -- ^ ( Facts about the given EIx
  --   , unknown times and time spans )
  --   The union of these facts and times and time spans should exactly
  --   equal the input time/time span.
spanLookupVFacts tspan vix = do
  tellDep (Dep_FactSpan tspan vix)
  facts <- valueFacts vix <$> untrackedAskFacts
  let knownFacts = T.cropTimeSpan tspan facts
      knownTSpans = either id (DS_Point . fst) . snd <$> T.elems knownFacts
      unknownTSpans = tspan `difference` knownTSpans
  return (knownFacts, unknownTSpans)

-- TODO rename all DerivationM primitives to `xyzM`

lookupM'
  :: Time
  -- ^ Time t too look up
  -> EIx a
  -> DerivationM (Maybe (DerivationTrace a, Either SpanExc (MaybeOcc a)))
  -- ^ If known, Left is the NoOcc fact's time span spanning t and Right is the
  -- Occ or NoOcc point fact at time t.
lookupM' t vix = do
  tellDep (Dep_FactSpan (DS_Point t) vix)
  T.lookup' t . valueFacts vix <$> untrackedAskFacts

lookupNegInf'
  :: EIx a
  -> DerivationM (Maybe (DerivationTrace a, SpanExc))
  -- ^ If known, the NoOcc span covering -Inf
lookupNegInf' vix = do
  tellDep (Dep_NegInf vix)
  T.lookupNegInf' . valueFacts vix <$> untrackedAskFacts

lookupJustAfter' :: Time -> EIx a -> DerivationM (Maybe (DerivationTrace a, SpanExc))
lookupJustAfter' t vix = do
  tellDep (Dep_JustAfter t vix)
  T.lookupJustAfter' t . valueFacts vix <$> untrackedAskFacts

lookupJustBefore' :: Time -> EIx a -> DerivationM (Maybe (DerivationTrace a, SpanExc))
lookupJustBefore' t vix = do
  tellDep (Dep_JustBefore t vix)
  T.lookupJustBefore' t . valueFacts vix <$> untrackedAskFacts

lookupAtStartOf' :: TimeSpan -> EIx a -> DerivationM (Maybe (DerivationTrace a, Either SpanExc (Time, MaybeOcc a)))
lookupAtStartOf' tts = case tts of
  DS_Point t -> (fmap . fmap . fmap . fmap) (t,) <$> lookupM' t
  DS_SpanExc ts -> (fmap . fmap . fmap) Left <$> case spanExcJustBefore ts of
    Nothing -> lookupNegInf'
    Just t -> lookupJustAfter' t



--
-- I need a way to relate new facts and new derivation-based-clearances to live
-- derivations via their dependencies (DrivationDep). I also need to deal with
-- the fact that multiple Derivations may be made "hot" (i.e. ready to be poked
-- due to a dependency change) due to a single dependency change, but we are
-- poking serially so may get even more hot Derivations before we've progressed
-- all the current hot derivations. I think we need dome unique ID per live
-- derivation and we should have a Set of live derivations that we'll use as a
-- queue of things to poke.
--
-- (EIx, TimeSpan) is a unique identifier for Derivations, though they may
-- change, but they only change after they are poked, so that sufficient for use
-- between pokes.
--


{- APPENDIX -}


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
  showPeakValueM (PrevV ix _) = "(PrevV " ++ show ix ++ " _)"
