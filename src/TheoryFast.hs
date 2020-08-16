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
import Data.Maybe (listToMaybe, fromJust)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Coerce (coerce)
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
import Control.Monad (when)
import Data.List (foldl')




{-


Changing the dirty flag in KnowledgeBase from Bool to something similar
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


  -- , kbDerivations :: Derivations
  -- -- | Is the KnowledgeBase dirty such that some derivations may be able to
  -- -- progress. This is set to False before attempting to progress all
  -- -- derivations.
  -- , kbDirty :: Bool


  -- WIP derivation tracking by deps
  , kbDerivations :: DerivationsByDeps
  , kbHotDerivations :: Set SomeDerivationID
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

-- Some data to store/query derivations according to their dependencies
data DerivationsByDeps = DerivationsByDeps
  { dbdNextID :: Int
  , dbdDerivation :: IntMap (DbdDerivation_Value Any) -- Map (DerivationID a) (VIx a, Derivation a)

  -- Derivations keyed on dependencies

  -- Ixs to DerivationIDs
  -- TODO and indexes, then update:
  --  * dbdDelete
  --  * dbdSetDeps
  --  * ???

  , dbdIxSpanLoJurisdiction :: Map (SomeVIx, Maybe Time) Int -- Map (VIx a, Maybe Time) DerivationID
  -- ^ Used for `dbdLookupSpanDerJustAfter`. Key is lot time of derivation
  -- jurisdiction. Only applies to (non-DeriveAfterFirstChange) derivations with
  -- a span jurisdiction. Nothing means (-Inf)
  }

type DbdDerivation_Value a = (VIx a, Derivation a)

-- | Get the key in to dbdIxSpanLoJurisdiction
dbdIxKeySpanLoJurisdiction :: VIx a -> Derivation a -> Maybe (SomeVIx, Maybe Time)
dbdIxKeySpanLoJurisdiction vix der = case der of
  Derivation _ (DS_SpanExc tspan) _ _ -> Just (SomeVIx vix, spanExcJustBefore tspan)
  _ -> Nothing


newtype DerivationID a = DerivationID Int
  deriving (Eq, Ord)
data SomeDerivationID = forall a . SomeDerivationID (VIx a) (DerivationID a)
instance Eq SomeDerivationID where
  (SomeDerivationID vixA derIdA) == (SomeDerivationID vixB derIdB)
    = vixA == coerce vixB && derIdA == coerce derIdB
instance Ord SomeDerivationID where
  compare (SomeDerivationID vixA derIdA) (SomeDerivationID vixB derIdB)
    = compare (vixA, derIdA) (coerce (vixB, derIdB))

dbdLookupDer :: DerivationID a -> DerivationsByDeps -> Maybe (VIx a, Derivation a)
dbdLookupDer (DerivationID derIdInt) dbd = fmap
  (unsafeCoerce :: DbdDerivation_Value Any -> DbdDerivation_Value a)
  (IM.lookup derIdInt (dbdDerivation dbd))

-- | Lookup a derivation that spans just after the given time.
dbdLookupSpanDerJustAfter
  :: VIx a
  -> Maybe Time
  -- ^ Nothing means -Inf
  -> DerivationsByDeps
  -> Maybe (DerivationID a, Derivation a)
dbdLookupSpanDerJustAfter vix t dbd = do
  let ix = dbdIxSpanLoJurisdiction dbd
  derId <- M.lookup (SomeVIx vix, t) ix
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

dbdInsertNoDeps :: VIx a -> Derivation a -> DerivationsByDeps -> (DerivationID a, DerivationsByDeps)
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
dbdSetDeps derID deps dbd = dbd

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

      pushHotDerivation derId = modify (\kb -> kb { kbHotDerivations = S.insert derId (kbHotDerivations kb) })

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
              -- If no progress, simply update the deps (they have changed).
              Nothing -> modify (\kb -> kb { kbDerivations = dbdSetDeps derId deps (kbDerivations kb) })
              -- Else we made progress and should add the new facts and (hot) derivations.
              Just (newFacts, newDers) -> do
                oldHotDers <- gets kbHotDerivations -- note we've already popped off derId
                let (newDerIds, newKbDers)
                      = dbdInsertsNoDeps (SomeDerivation vix <$> newDers)
                      $ dbdDelete derId allDers
                    newKbHotDers = S.union (S.fromList newDerIds) oldHotDers
                modify (\kb -> kb
                  { kbDerivations = newKbDers
                  , kbHotDerivations = newKbHotDers
                  })

      -- loop_OLD i = do
      --     if i == n
      --       then return ()
      --       else do
      --         allDers <- gets kbDerivations
      --         allFacts <- gets kbFacts
      --         case allDers !! i of
      --           SomeDerivation vix der -> do
      --             -- case pokeDerivation vix allDers allFacts der of
      --             let (mayNewFactsAndDers, (), deps) = runRWS (pokeDerivation vix der) (allFacts, allDers) ()
      --             case mayNewFactsAndDers of
      --               Nothing -> do
      --                 -- TODO Poke this derivation when `deps` have changed
      --                 loop (i + 1)
      --               Just (newFacts, newDers) -> do
      --                 modify (\_ -> KnowledgeBase
      --                   { kbFacts = (singletonFacts vix newFacts) <> allFacts
      --                   , kbDerivations = (SomeDerivation vix <$> newDers) <> take i allDers <> drop (i+1) allDers
      --                   , kbDirty = True
      --                   })

  -- This is the important part. Is corresponds to the `deriveE` denotation.
  pokeDerivation
    :: forall a
    .  VIx a
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
      Derivation dtrace ttspan prevDeps contDerivation -> case contDerivation of
        Pure a ->if null prevDeps
          then pure $ Just $ case ttspan of
              DS_Point t -> let
                dtrace' = appendDerTrace dtrace $
                  "Jurisdiction is a point (t=" ++ show t ++ "), ValueM is `Pure a`."
                in (T.singleton (DS_Point t) (dtrace', a), [])

              DS_SpanExc tspanSpan -> let
                dtrace' = appendDerTrace dtrace $
                  "Jurisdiction is (" ++ show tspanSpan ++ "), ValueM is `Pure a`."
                in (T.singleton (DS_SpanExc tspanSpan) (dtrace', a), [])
          else stepCompleteWithPrevDeps a
        GetV vixb cont -> do
          factsBAndUnknownsMay <- if null prevDeps
                then Just <$> spanLookupVFacts ttspan vixb

                -- chronological version of the above with PrevV deps.
                -- TODO this and the above "then" and also the PrevV cases
                -- have very similar code (split on other facts). Try to DRY
                -- it.
                else do
                  valMay <- lookupAtStartOf' ttspan vixb
                  pure $ case valMay of
                    Nothing -> Nothing
                    Just (ttspanB, b) -> Just
                      ( T.singleton (fromJust $ ttspanB `intersect` ttspan) b
                      , ttspan `difference` ttspanB
                      )

          pure $ case factsBAndUnknownsMay of
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
                                  ("Split on GetV dep (" ++ show vixb ++ ") Fact_SpanExc")
                      in (T.empty, [newDer])
                    DS_Point t -> let
                        newCont = cont valB
                        newDer  = Derivation dtrace (DS_Point t) prevDeps newCont
                                  `withDerTrace`
                                  ("Split on GetV dep (" ++ show vixb ++ ") Fact_Point")
                        in (T.empty, [newDer])
                  | (ttspanB, (_, valB)) <- T.elems factsB
                  ]
                <>
                -- For unknowns, simply split the derivation into the
                -- unknown subspans.
                ( T.empty
                , [ Derivation dtrace subTspan prevDeps contDerivation
                    `withDerTrace`
                    ("Split on GetV dep (" ++ show vixb ++ ") unknown point or span.")
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
          DS_Point t -> do
            mayPrevVB <- lookupPrevV t eixB predicate
            pure $ case mayPrevVB of
              Unknown -> Nothing
              Known prevBMay -> Just $ let
                newCont = mayPrevToCont prevBMay
                newDer  = Derivation dtrace ttspan (SomeVIx eixB : prevDeps) newCont
                      `withDerTrace`
                      ("Use known PrevV value of dep (" ++ show eixB ++ ")")
                in (T.empty, [newDer])
              _ -> undefined

          -- !! The Plan
          -- !! Try and split on facts about eixB.
          DS_SpanExc tspan -> do
            prevVSpans <- spanLookupPrevV ttspan eixB predicate
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
                        Just tLo -> lookupCurrV tLo eixB predicate
                  return $ case prevValMayIfKnown of
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
                    newDer  = Derivation dtrace ttspan' prevDeps newCont
                        `withDerTrace`
                          ("Split on known facts")
                    in (T.empty, [newDer])
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
          -> DerivationM (Maybe (ValueTimeline a, [Derivation a]))
            -- ^ Taking into account the PrevV deps, if progress can be made,
            -- return the new Facts(s) and any new Derivation(s).
        stepCompleteWithPrevDeps val = case ttspan of

          -- If the ttspan is a point time, then this is easy! Pure x means x.
          DS_Point t -> let
              dtrace' = appendDerTrace dtrace $
                "ValueM is (Pure _). As jurisdiction is a point, we can ignore PrevV deps."
              in return $ Just (T.singleton (DS_Point t) (dtrace', val), [])

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
            ctMay <- clearanceTime (SomeVIx eix) tLoMay
            return $ case ctMay of
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
            :: [SomeVIx]
              -- ^ Stack of `VIx`s to visit
            -> S.Set SomeVIx
              -- ^ visited `VIx`s
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
          -- single VIx.
          neighborsAndClearance
            :: SomeVIx
            -> DerivationM (Maybe ([SomeVIx], Maybe Time))
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
            :: SomeVIx
            -> DerivationM (Maybe (Maybe Time))
          neighborsAndClearanceByFacts (SomeVIx ix) = findClearanceAfter tLo
            where
            findClearanceAfter :: Maybe Time -> DerivationM (Maybe (Maybe Time))
            findClearanceAfter tMay = do
              mayFactSpan <- fmap fst <$> case tMay of
                Nothing -> lookupNegInf' ix
                Just t  -> lookupJustAfter' t ix
              return $ case mayFactSpan of
                Just (DS_SpanExc clearanceSpan) -> Just (spanExcJustAfter clearanceSpan)
                Just (DS_Point _) -> error "Implossible!"
                Nothing -> Nothing

          -- | Get the neighbors (PrevV deps) and local clearance time of a
          -- single VIx. Only considers active Derivations, not facts.
          neighborsAndClearanceByDerivation
            :: SomeVIx
            -> DerivationM (Maybe ([SomeVIx], Maybe Time))
          neighborsAndClearanceByDerivation someDepIx@(SomeVIx depIx) = do
            tellDep (Dep_DerivationClearance tLo depIx)
            derMay <- dbdLookupSpanDerJustAfter depIx tLo <$> untrackedAskDerivations
            return $ case derMay of
              Just ( _
                   , Derivation
                        _
                        (DS_SpanExc tspan) -- Must be of this form due to `dbdLookupSpanDerJustAfter`
                        neighbors
                        (Pure _)
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
  -> DerivationM FirstValueChange
searchForFirstChange tspan vix = do
  (factsTl, _) <- spanLookupVFacts (DS_SpanExc tspan) vix
  let facts = T.elems factsTl
  return $ case facts of
    [] -> Other
    (DS_SpanExc t0, _) : _
      | t0 == tspan -> NoChangeInSpan
      -- t0 is a strict subset of tspan. Here we test that they have the same
      -- lower bound. Hence t0's upper bound is not Inf.
      | spanExcSameLowerBound t0 tspan -> FirstChangeIsAt (fromJust (spanExcJustAfter t0))
      -- t0 is strict subset of tspan and doesn't start at the same lower bound.
      -- Hence the t0's lower bound must not be -Inf.
      | otherwise -> FirstChangeIsAtOrBefore (fromJust (spanExcJustBefore t0))

-- | Directly look up the previous value that satisfies the predicate
-- (strictly before the given time).
lookupPrevV
  :: Time
  -- ^ Time t
  -> VIx a
  -- ^ Event to lookup.
  -> (a -> Maybe b)
  -- ^ predicate / projection.
  -> DerivationM (MaybeKnown (Maybe b))
  -- ^ Unknown: if unknown
  -- Known Nothing: if no value satisfying the predicate occurs strictly before t.
  -- Known (Just b): the latest (projected) value satisfying the predicate (strictly before time t).
lookupPrevV t vix predicate = do
  vMay <- lookupJustBefore' t vix
  case vMay of
    Nothing -> return Unknown
    Just (ttspan, (_, a)) -> case ttspan of
      DS_Point _ -> error "Impossible! lookupJustBefore' can't return a point"
      DS_SpanExc tspan -> case predicate a of
        Just b -> return $ Known (Just b)
        Nothing -> case spanExcJustBefore tspan of
                  Nothing -> return $ Known Nothing
                  Just tLo -> lookupCurrV tLo vix predicate

-- | Directly look up the current (i.e. latest) event occurrence (equal or before the given time).
lookupCurrV
  :: Time
  -- ^ Time t
  -> VIx a
  -- ^ Event to lookup.
  -> (a -> Maybe b)
  -- ^ predicate / projection.
  -> DerivationM (MaybeKnown (Maybe b))
  -- ^ Unknown: if unknown
  -- Known Nothing: if no value satisfying the predicate occurs at or before t.
  -- Known (Just b): the latest (projected) value satisfying the predicate (at or before t).
lookupCurrV t eix predicate = do
  aMay <- lookupM' t eix
  case aMay of
    Nothing -> return Unknown
    Just (ttspan', (_, a)) -> case predicate a of
      Nothing -> case ttspan' of
        DS_Point t' -> lookupPrevV t' eix predicate
        DS_SpanExc tspan' -> case spanExcJustBefore tspan' of
          Nothing -> return (Known Nothing)
          Just t' -> lookupCurrV t' eix predicate
      Just b -> return (Known (Just b))

-- | Directly lookup the previous value for an event over a span of time.
spanLookupPrevV
  :: TimeSpan
  -- ^ Time or span to lookup
  -> VIx a
  -- ^ Event to lookup
  -> (a -> Maybe b)
  -- ^ predicate / projection.
  -> DerivationM ([(TimeSpan, Maybe b)], [TimeSpan])
  -- ^ ( Known values about the given VIx
  --   , unknown times and time spans )
  --   The union of these times and time spans should exactly
  --   equal the input time/time span.
spanLookupPrevV tspan eix predicate = do
  facts <- prevVFacts tspan eix predicate
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
  :: forall a b
  .  TimeSpan
  -- ^ Time or span to lookup
  -> VIx a
  -- ^ Event to lookup
  -> (a -> Maybe b)
  -- ^ predicate / projection.
  -> DerivationM [(TimeSpan, Maybe b)]
  -- ^ All known previous event values (if one exists)
prevVFacts timeSpan vix predicate = do
  (factsTl, _) <- spanLookupVFacts timeSpan vix
  fs' <- sequence
    [ case ttspan of
      DS_SpanExc tspan -> do
        mayPrevVMay :: MaybeKnown (Maybe b) <- case spanExcJustBefore tspan of
          -- Span starts at -∞ so that's a known Nothing previous event
          Nothing -> pure (Known Nothing)
          -- Span starts at a time prevT
          Just prevT -> lookupCurrV prevT vix predicate
        return $ case mayPrevVMay of
            Unknown -> []
            Known prevVMay -> (DS_SpanExc tspan, prevVMay) : [(DS_Point nextT, prevVMay) | Just nextT <- [spanExcJustAfter tspan]]
            _ -> undefined
      DS_Point _ -> pure [] -- Point knowledge is handled by the above case
    | (ttspan, _) <- T.elems factsTl
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
  = forall a . Dep_FactSpan TimeSpan (VIx a)
  -- Depend on all the value at -Inf a Vix
  | forall a . Dep_NegInf (VIx a)
  -- Depend on all the value just after t of a Vix
  | forall a . Dep_JustBefore Time (VIx a)
  -- Depend on all the value just before t of a Vix
  | forall a . Dep_JustAfter Time (VIx a)
  -- Depend on the derivation based clearance of a Vix just after a given time.
  -- That's a completed (continuation is Pure _) Derivation spanning a time just
  -- after the given time. (Nothing means -Inf)
  | forall a . Dep_DerivationClearance (Maybe Time) (VIx a)

--
-- DerivationM Primitives
--

-- | Directly look up all known facts for a given VIx and time or time span.
--
-- TODO This causes a dep on the whole span, but at the use sights we may be
-- using less info.
spanLookupVFacts
  :: TimeSpan
  -- ^ Time or span to lookup
  -> VIx a
  -- ^ Event to lookup
  -- ^ All known facts.
  -> DerivationM (ValueTimeline a, [TimeSpan])
  -- ^ ( Facts about the given VIx
  --   , unknown times and time spans )
  --   The union of these facts and times and time spans should exactly
  --   equal the input time/time span.
spanLookupVFacts tspan vix = do
  tellDep (Dep_FactSpan tspan vix)
  facts <- valueFacts vix <$> untrackedAskFacts
  let knownFacts = T.cropTimeSpan tspan facts
      knownTSpans = fst <$> T.elems knownFacts
      unknownTSpans = tspan `difference` knownTSpans
  return (knownFacts, unknownTSpans)

-- TODO rename all DerivationM primitives to `xyzM`

lookupM' :: Time -> VIx a -> DerivationM (Maybe (TimeSpan, (DerivationTrace a, a)))
lookupM' t vix = do
  tellDep (Dep_FactSpan (DS_Point t) vix)
  T.lookup' t . valueFacts vix <$> untrackedAskFacts

lookupNegInf' :: VIx a -> DerivationM (Maybe (TimeSpan, (DerivationTrace a, a)))
lookupNegInf' vix = do
  tellDep (Dep_NegInf vix)
  T.lookupNegInf' . valueFacts vix <$> untrackedAskFacts

lookupJustAfter' :: Time -> VIx a -> DerivationM (Maybe (TimeSpan, (DerivationTrace a, a)))
lookupJustAfter' t vix = do
  tellDep (Dep_JustAfter t vix)
  T.lookupJustAfter' t . valueFacts vix <$> untrackedAskFacts

lookupJustBefore' :: Time -> VIx a -> DerivationM (Maybe (TimeSpan, (DerivationTrace a, a)))
lookupJustBefore' t vix = do
  tellDep (Dep_JustBefore t vix)
  T.lookupJustBefore' t . valueFacts vix <$> untrackedAskFacts

lookupAtStartOf' :: TimeSpan -> VIx a -> DerivationM (Maybe (TimeSpan, (DerivationTrace a, a)))
lookupAtStartOf' tts = case tts of
  DS_Point t -> lookupM' t
  DS_SpanExc ts -> case spanExcJustBefore ts of
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
-- (VIx, TimeSpan) is a unique identifier for Derivations, though they may
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
