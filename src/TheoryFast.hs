{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
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

module TheoryFast
  ( module TheoryFast
  , module Theory
  ) where

-- import Control.Monad (when)
import Control.Monad.Trans.State.Strict (State, execState, gets, modify)
import Control.Monad.Trans.RWS.CPS (asks, RWS, runRWS, tell)
-- import Data.Hashable
-- import Data.Kind
import           Data.Coerce (coerce)
import qualified Data.IntMap as IM
import           Data.IntMap (IntMap)
import           Data.List (find)
import qualified Data.Map as M
import           Data.Map (Map)
import           Data.Maybe (fromMaybe, fromJust)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.String
import           Data.Text.Prettyprint.Doc
import           Unsafe.Coerce
import           GHC.Exts (Any)
import           Safe (headMay, minimumMay)

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
  (withDerTrace,  factTrace
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
  , mkDerivationForAllTime

  , TimeSpan(..)
  , factTSpan

  , DerivationTrace
  , DerivationTraceEl
  , appendDerTrace

  , getE
  , currV
  , prevV
  , requireE
  )
-- import Control.Monad (when)
import Data.List (foldl')
import Data.Kind (Type)
import Control.Monad (forM)


-- | Facts about a single value.
type ValueTimeline a = Timeline (DerivationTrace a) a
-- | Derivation clearances about a single value (keys are tLo, values are (trace, prevV deps, tHi)).
type ValueDerivationClearances a = Map (Maybe Time) (DerivationTrace a, [SomeEIx], Maybe Time)
data FactsEl a = FactsEl
  { factsElTimeline             :: ValueTimeline a
  -- ^ Timeline of the value.
  , factsElDerivationClearances :: ValueDerivationClearances a
  -- ^ Derivation clearances.
  }

instance Semigroup (FactsEl a) where
  (FactsEl tlA csA) <> (FactsEl tlB csB)
    = FactsEl
        (tlA <> tlB)
        (M.unionWith max csA csB) -- Take the higher clearance (I don't think we'll ever have duplicate keys though).

-- | A bunch of facts about possibly many values.
type Facts = DMap EIx FactsEl

listToFacts :: [Th.SomeFact] -> Facts
listToFacts someValueFacts
  | not (null errs) = error $ unlines errs
  | otherwise = fs
  where
  errs = concat
    [ ((show k ++ ": ") ++) <$> T.checkTimeline tl
    | DM.SomeIx k <- DM.keys fs
    , let tl = factsElTimeline (fs DM.! k)
    ]
  fs = DM.fromListWith (<>)
    [ DM.El
        eix
        (case fact of
          Th.Fact_VFact vfact -> FactsEl
            (case vfact of
              Th.VFact_NoOcc derT tts -> T.singletonNoOcc derT tts
              Th.VFact_Occ   derT t a -> T.singletonOcc   derT t a
            )
            M.empty
          Th.Fact_DerivationClearance derT deps ts -> FactsEl
            T.empty
            (M.singleton (spanExcJustBefore ts) (derT, deps, spanExcJustAfter ts))
        )
    | Th.SomeFact eix fact <- someValueFacts
    ]

singletonFacts :: EIx a -> FactsEl a -> Facts
singletonFacts eix el = DM.singleton eix el

valueFacts :: EIx a -> Facts -> ValueTimeline a
valueFacts eix facts = maybe T.empty factsElTimeline (DM.lookup eix facts)

data KnowledgeBase = KnowledgeBase
  { kbFacts :: Facts

  -- Derivation/Dependency tracking
  , kbDerivations :: DerivationsByDeps
  -- TODO I don't think we actually need to store this in the record.
  , kbHotDerivations :: Set SomeDerivationID
  }

kbValueFacts :: EIx a -> KnowledgeBase -> ValueTimeline a
kbValueFacts vix kb = valueFacts vix (kbFacts kb)

lookupVKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
lookupVKB t eix kb = lookupV t eix (kbFacts kb)

lookupVKBTrace :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (DerivationTrace a)
lookupVKBTrace t eix kb = lookupVTrace t eix (kbFacts kb)

-- | Lookup the latest known event at or before the given time.
lookupLatestKnownKB :: Time -> EIx a -> KnowledgeBase -> Maybe a
lookupLatestKnownKB t eix kb = lookupLatestKnown t eix (kbFacts kb)

lookupV :: Time -> EIx a -> Facts -> MaybeKnown (MaybeOcc a)
lookupV t eix facts = snd <$> lookupVFact t eix facts

lookupVTrace :: Time -> EIx a -> Facts -> MaybeKnown (DerivationTrace a)
lookupVTrace t vix facts = fst <$> lookupVFact t vix facts

lookupVFact :: Time -> EIx a -> Facts -> MaybeKnown (DerivationTrace a, MaybeOcc a)
lookupVFact t vix facts = MaybeKnown $ do
  let vfs = valueFacts vix facts
  (tr, eitherNoOccSpanOrOcc) <- T.lookup' t vfs
  return (tr, either (const NoOcc) id eitherNoOccSpanOrOcc)

-- | Lookup the latest known event at or before the given time.
lookupLatestKnown :: Time -> EIx a -> Facts -> Maybe a
lookupLatestKnown t eix facts
  = headMay
      [ a
      | (_, Right (_, a))
          <- T.elemsRev
          $ T.select (Span Open (ClosedInc t))
          $ valueFacts eix facts
      ]

type KnowledgeBaseM a = State KnowledgeBase a

-- Some data to store/query derivations according to their dependencies
data DerivationsByDeps = DerivationsByDeps
  { dbdNextID :: Int
  , dbdDerivation :: IntMap (DbdDerivation_Value Any) -- Map (DerivationID a) (EIx a, Derivation a)
  , dbdDerivationDeps :: Map SomeDerivationID [DerivationDep]

  -- Derivations keyed on dependencies

  -- Ixs to DerivationIDs
  -- TODO and indexes, then update:
  --  * dbdDelete
  --  * dbdSetDeps
  --  * ???

  -- TODO I can probably replace Derivation based clearance with a new type of Clearance fact.
  , dbdIxSpanLoJurisdiction :: Map (SomeEIx, Maybe Time) Int -- Map (EIx a, Maybe Time) DerivationID
  -- ^ Used for `dbdLookupSpanDerJustAfter`. Key is lo time of derivation
  -- jurisdiction. Only applies to (non-DeriveAfterFirstChange) derivations with
  -- a span jurisdiction. Nothing means (-Inf).
  -- Used for: Dep_DerivationClearance (Maybe Time) (EIx a) ??????????

  , dbdIxDepOnFactSpan :: Map SomeEIx (MultiTimeline SomeDerivationID)
  -- ^ (dbdIxDepOnFactSpan ! eix) `MT.select` span = derivations that depend on eix at span.
  -- Used for: Dep_FactSpan TimeSpan (EIx a)

  , dbdIxDepOnNegInf :: Map SomeEIx (Set SomeDerivationID)
  -- ^ (dbdIxDepOnNegInf ! eix) = derivations that depend on eix at -Inf.
  -- Used for: Dep_NegInf (EIx a)

  , dbdIxDepOnJustBefore :: Map SomeEIx (Map Time (Set SomeDerivationID))
  -- ^ (dbdIxDepOnJustBefore ! eix) ! t = derivations that depend on eix just before t.
  -- Used for: Dep_JustBefore Time (EIx a)

  , dbdIxDepOnJustAfter :: Map SomeEIx (Map Time (Set SomeDerivationID))
  -- ^ (dbdIxDepOnJustAfter ! eix) ! t = derivations that depend on eix just after t.
  -- Used for: Dep_JustAfter Time (EIx a)

  , dbdIxDepOnDerivationClearance :: Map SomeEIx (Map (Maybe Time) (Set SomeDerivationID))
  -- ^ (dbdIxDepOnJustAfter ! eix) ! t = derivations that depend on clearance of
  -- eix at t (Nothing means -Inf).
  -- Used for: Dep_DerivationClearance (Maybe Time) (EIx a)
  }

type DbdDerivation_Value a = (EIx a, Derivation a)

-- | Get the key in to dbdIxSpanLoJurisdiction
dbdIxKeySpanLoJurisdiction :: EIx a -> Derivation a -> Maybe (SomeEIx, Maybe Time)
dbdIxKeySpanLoJurisdiction vix der = case der of
  Derivation _ (DS_SpanExc tspan) _ _ _ -> Just (SomeEIx vix, spanExcJustBefore tspan)
  _ -> Nothing

newtype DerivationID (a :: Type) = DerivationID Int
  deriving (Eq, Ord, Show)
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
  , dbdDerivationDeps = M.empty
  , dbdIxSpanLoJurisdiction = M.empty
  , dbdIxDepOnFactSpan = M.empty
  , dbdIxDepOnNegInf = M.empty
  , dbdIxDepOnJustBefore = M.empty
  , dbdIxDepOnJustAfter = M.empty
  , dbdIxDepOnDerivationClearance = M.empty
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
    , dbdDerivationDeps = dbdDerivationDeps dbd
    , dbdIxSpanLoJurisdiction = case dbdIxKeySpanLoJurisdiction vix der of
        Just key -> M.insert key myIdInt (dbdIxSpanLoJurisdiction dbd)
        Nothing -> dbdIxSpanLoJurisdiction dbd

    -- No new deps so dep indexes stay the same.
    , dbdIxDepOnFactSpan   = dbdIxDepOnFactSpan   dbd
    , dbdIxDepOnNegInf     = dbdIxDepOnNegInf     dbd
    , dbdIxDepOnJustBefore = dbdIxDepOnJustBefore dbd
    , dbdIxDepOnJustAfter  = dbdIxDepOnJustAfter  dbd
    , dbdIxDepOnDerivationClearance  = dbdIxDepOnDerivationClearance dbd
    }
  )
  where
  myIdInt = dbdNextID dbd
  myId = DerivationID myIdInt

dbdDelete :: DerivationID a -> DerivationsByDeps -> DerivationsByDeps
dbdDelete derId@(DerivationID derIdInt) dbd = case IM.lookup derIdInt (dbdDerivation dbd) of
  Nothing -> dbd
  Just (vix, der) -> DerivationsByDeps
    { dbdNextID = dbdNextID dbd
    , dbdDerivation = IM.delete derIdInt (dbdDerivation dbd)
    , dbdDerivationDeps = M.delete someDerId (dbdDerivationDeps dbd)
    , dbdIxSpanLoJurisdiction = case dbdIxKeySpanLoJurisdiction vix der of
        Nothing -> dbdIxSpanLoJurisdiction dbd
        Just key -> M.delete key (dbdIxSpanLoJurisdiction dbd)
    , dbdIxDepOnFactSpan = foldl'
        (\ix someEix -> alterMT (MT.deleteVal someDerId) someEix ix)
        (dbdIxDepOnFactSpan dbd)
        [SomeEIx dix | Dep_FactSpan _ dix <- deps]
    , dbdIxDepOnNegInf = foldl'
        (\ix someEix -> alterSet (S.delete someDerId) someEix ix)
        (dbdIxDepOnNegInf dbd)
        [SomeEIx dix | Dep_NegInf dix <- deps]
    , dbdIxDepOnJustBefore = foldl'
        (\ix (t, someEix) -> alterMap (alterSet (S.delete someDerId) t) someEix ix)
        (dbdIxDepOnJustBefore dbd)
        [(t, SomeEIx dix) | Dep_JustBefore t dix <- deps]
    , dbdIxDepOnJustAfter = foldl'
        (\ix (t, someEix) -> alterMap (alterSet (S.delete someDerId) t) someEix ix)
        (dbdIxDepOnJustAfter dbd)
        [(t, SomeEIx dix) | Dep_JustAfter t dix <- deps]
    , dbdIxDepOnDerivationClearance = foldl'
        (\ix (tmay, someEix) -> alterMap (alterSet (S.delete someDerId) tmay) someEix ix)
        (dbdIxDepOnDerivationClearance dbd)
        [(tmay, SomeEIx dix) | Dep_DerivationClearance tmay dix <- deps]
    }
    where
    someDerId = SomeDerivationID vix (unsafeCoerce derId)
    deps = fromMaybe [] (M.lookup someDerId (dbdDerivationDeps dbd))

dbdSetDeps :: forall a . DerivationID a -> [DerivationDep] -> DerivationsByDeps -> DerivationsByDeps
dbdSetDeps derId deps dbd = DerivationsByDeps
    { dbdNextID = dbdNextID dbd
    , dbdDerivation = dbdDerivation dbd
    , dbdDerivationDeps = M.insert someDerId deps (dbdDerivationDeps dbd)
    , dbdIxSpanLoJurisdiction = dbdIxSpanLoJurisdiction dbd
    , dbdIxDepOnFactSpan = foldl'
        (\ix (ts, someEix) -> alterMT (MT.insertTimeSpan ts someDerId) someEix ix)
        (dbdIxDepOnFactSpan dbdMid)
        [(ts, SomeEIx dix) | Dep_FactSpan ts dix <- deps]
    , dbdIxDepOnNegInf = foldl'
        (\ix someEix -> alterSet (S.insert someDerId) someEix ix)
        (dbdIxDepOnNegInf dbdMid)
        [SomeEIx dix | Dep_NegInf dix <- deps]
    , dbdIxDepOnJustBefore = foldl'
        (\ix (t, someEix) -> alterMap (alterSet (S.insert someDerId) t) someEix ix)
        (dbdIxDepOnJustBefore dbdMid)
        [(t, SomeEIx dix) | Dep_JustBefore t dix <- deps]
    , dbdIxDepOnJustAfter = foldl'
        (\ix (t, someEix) -> alterMap (alterSet (S.insert someDerId) t) someEix ix)
        (dbdIxDepOnJustAfter dbdMid)
        [(t, SomeEIx dix) | Dep_JustAfter t dix <- deps]
    , dbdIxDepOnDerivationClearance = foldl'
        (\ix (tmay, someEix) -> alterMap (alterSet (S.insert someDerId) tmay) someEix ix)
        (dbdIxDepOnDerivationClearance dbdMid)
        [(tmay, SomeEIx dix) | Dep_DerivationClearance tmay dix <- deps]
    }
    where
    DerivationID derIdInt = derId
    someDerId = SomeDerivationID
                  ((unsafeCoerce :: EIx Any -> EIx a)
                      $ fst
                      $ dbdDerivation dbd IM.! derIdInt
                  )
                  derId
    dbdMid = dbdDelete derId dbd

alterMT :: Ord k => (MultiTimeline a -> MultiTimeline a) -> k -> Map k (MultiTimeline a) -> Map k (MultiTimeline a)
alterMT f k m  = M.alter (\m' -> let x = f (fromMaybe MT.empty m') in if MT.null x then Nothing else Just x) k m

alterMap :: Ord k1 => (Map k2 a -> Map k2 a) -> k1 -> Map k1 (Map k2 a) -> Map k1 (Map k2 a)
alterMap f k m = M.alter (\m' -> let x = f (fromMaybe M.empty  m') in if  M.null x then Nothing else Just x) k m

alterSet :: Ord k => (Set a -> Set a) -> k -> Map k (Set a) -> Map k (Set a)
alterSet f k m = M.alter (\s  -> let x = f (fromMaybe S.empty  s ) in if  S.null x then Nothing else Just x) k m

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
dbdAffectedDers newDers newFacts dbd = S.unions $
  -- Dep_DerivationClearance
  -- Derivation based clearance only changes when the derivation is complete
  -- and a span. dbdIxDepOnDerivationClearance is keyed on the low time.
  [ fromMaybe S.empty
    $ M.lookup tLo
    $ fromMaybe M.empty
    $ M.lookup newDerSomeEIx
    $ dbdIxDepOnDerivationClearance dbd

    | SomeDerivation newDerEIx Derivation
        { derContDerivation = Pure _
        , derTtspan = DS_SpanExc sp
        } <- newDers
    , let newDerSomeEIx = SomeEIx newDerEIx
    , let tLo = spanExcJustBefore sp
  ] ++
  (concat [ concat [
    -- Dep_FactSpan
    [ S.fromList
      $ MT.elems
      $ MT.select newFactSpan
      $ fromMaybe MT.empty
      $ M.lookup newFactSomeEIx (dbdIxDepOnFactSpan dbd)
    ]

    -- Dep_NegInf
    , [ fromMaybe S.empty $ M.lookup newFactSomeEIx (dbdIxDepOnNegInf dbd)
      | spanLo newFactSpan == Open
      ]

    -- Dep_JustBefore
    , lookupJustBefore newFactSpan
      $ fromMaybe M.empty
      $ M.lookup newFactSomeEIx (dbdIxDepOnJustBefore dbd)

    -- Dep_JustAfter
    , lookupJustAfter newFactSpan
      $ fromMaybe M.empty
      $ M.lookup newFactSomeEIx (dbdIxDepOnJustAfter dbd)
    ]

    | DM.SomeIx newFactEIx <- DM.keys newFacts
    , (_, eitherNoOccSpanOrOcc) <- T.elems (valueFacts newFactEIx newFacts)
    , let newFactSomeEIx = SomeEIx newFactEIx
    , let newFactSpan = case eitherNoOccSpanOrOcc of
            Left tspan -> timeSpanToSpan tspan
            Right (t, _) -> timeToSpan t
  ])
  where
  lookupJustBefore :: Span -> Map Time (Set SomeDerivationID) -> [Set SomeDerivationID]
  lookupJustBefore
    (Span loBound hiBound)  -- Span of the new fact
    jbDeps                  -- Deps keyed on the JustBefore time they depend on.
    = M.elems jbDeps'
    where
    -- Apply lower bound
    n_loBound = case loBound of
        Open -> jbDeps
        ClosedInc t -> M.dropWhileAntitone (<=t) jbDeps
        ClosedExc t -> M.dropWhileAntitone (<=t) jbDeps
    -- Apply upper bound
    jbDeps' =  case hiBound of
        Open -> n_loBound
        ClosedInc t -> M.takeWhileAntitone (<=t) n_loBound
        ClosedExc t -> M.takeWhileAntitone (<=t) n_loBound

  lookupJustAfter :: Span -> Map Time (Set SomeDerivationID) -> [Set SomeDerivationID]
  lookupJustAfter
    (Span loBound hiBound)  -- Span of the new fact
    jbDeps                  -- Deps keyed on the JustAfter time they depend on.
    = M.elems jbDeps'
    where
    -- Apply lower bound
    n_loBound = case loBound of
        Open -> jbDeps
        ClosedInc t -> M.dropWhileAntitone (<t) jbDeps
        ClosedExc t -> M.dropWhileAntitone (<t) jbDeps
    -- Apply upper bound
    jbDeps' =  case hiBound of
        Open -> n_loBound
        ClosedInc t -> M.takeWhileAntitone (<t) n_loBound
        ClosedExc t -> M.takeWhileAntitone (<t) n_loBound


-- Now a natural fist attempt at a solution is obvious: start with an initial
-- knowledge base and continue evaluating derivations until all terminate or
-- deadlock:

insertFacts :: Facts -> KnowledgeBase -> KnowledgeBase
insertFacts fs = execState (insertFactsAndDers fs [])

insertFactsAndDers :: Facts -> [SomeDerivation] -> KnowledgeBaseM ()
insertFactsAndDers newFacts newSomeDers = do
  oldHotDers <- gets kbHotDerivations -- note we've already popped off derId
  oldDers <- gets kbDerivations -- note we've already popped off derId
  let (newDerIds, newKbDers) = dbdInsertsNoDeps newSomeDers oldDers
      newKbHotDers
        = oldHotDers
        -- New derivations are all hot (we haven't calculated their deps yet)
        <> S.fromList newDerIds
        -- As dependencies have changed, more Derivations may be hot.
        <> dbdAffectedDers newSomeDers newFacts newKbDers
  modify (\kb -> KnowledgeBase
    { kbFacts = kbFacts kb <> newFacts
    , kbDerivations = newKbDers
    , kbHotDerivations = newKbHotDers
    })
  iterateWhileHot

mkKnowledgeBase :: Inputs -> KnowledgeBase
mkKnowledgeBase inputs = execState iterateWhileHot initialKb
  where
  (initialSomeFacts, initialSomeDerivations) = Th.inputsToInitialFactsAndDerivations inputs
  (initialDerivationIDs, initialDerivations) = dbdInitialFromListNoDeps initialSomeDerivations
  initialKb = KnowledgeBase
                { kbFacts = listToFacts initialSomeFacts
                , kbDerivations = initialDerivations
                , kbHotDerivations = S.fromList initialDerivationIDs
                }

iterateWhileHot :: KnowledgeBaseM ()
iterateWhileHot = do
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
        Nothing -> do
          modify (\kb -> kb { kbDerivations = dbdSetDeps derId deps (kbDerivations kb) })
          iterateWhileHot
        -- Else we made progress and should add the new facts and (hot) derivations.
        Just (newFactsEl, newDers) -> do
          modify (\kb -> kb { kbDerivations = dbdDelete derId (kbDerivations kb) })
          let newSomeDers = SomeDerivation vix <$> newDers
              newFacts = singletonFacts vix newFactsEl
          insertFactsAndDers newFacts newSomeDers
  where
  -- Try remove a derivation from kbHotDerivations
  popHotDerivation = do
    mvMay <- gets (S.minView . kbHotDerivations)
    case mvMay of
      Nothing -> return Nothing
      Just (derId, newHotDers) -> do
        modify (\kb -> kb { kbHotDerivations = newHotDers })
        return (Just derId)

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
    -> DerivationM (Maybe (FactsEl a, [Derivation a]))
    -- ^ Nothing if no progress. Else Just the new facts and new derivations.
  pokeDerivation eix derivation = do
    steppedMay <- case derivation of
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

        GetE (eixb :: EIx b) cont -> do
          let fromKnowns
                :: ValueTimeline b
                -> [Derivation a]
              fromKnowns factsB =
                [ case factIshB of
                    Left bTs -> Derivation dtrace bTs prevDeps (cont NoOcc) seenOcc
                          `withDerTrace`
                          ("Split on GetE dep (" ++ show eixb ++ ") VFact_NoOcc")
                    Right (bT, valB) -> Derivation dtrace (DS_Point bT) prevDeps (cont (Occ valB)) True
                          `withDerTrace`
                          ("Split on GetE dep (" ++ show eixb ++ ") VFact_Occ")
                | (_, factIshB) <- T.elems factsB
                ]
          if null prevDeps
          then do
            (factsB, unknowns) <- spanLookupVFacts ttspan eixb
            pure $ if T.null factsB
              then Nothing
              else Just
                    -- For unknowns, simply split the derivation into the
                    -- unknown subspans.
                    ( T.empty
                    , [ Derivation dtrace subTspan prevDeps contDerivation seenOcc
                          `withDerTrace`
                          ("Split on GetE dep (" ++ show eixb ++ ") which has unknown value at " ++ show subTspan)
                      | subTspan <- unknowns
                      ]
                      -- For knowns, split and try to progress the derivation.
                      ++ fromKnowns factsB
                    )

          -- Solve chronologically
          else do
            valMay <- lookupAtStartOf' ttspan eixb
            return $ case valMay of
              Nothing -> Nothing
              Just (tr, factIsh) -> let
                -- The point and span covering the rest of the jurisdiction.
                -- Nothing if `fact` already covers the full jurisdiction.
                nextPointMay :: Maybe (Time, SpanExc)
                nextPointMay = case factIsh of
                  Right _ -> Nothing -- implies that ttspan is a point, hence we cover it all.
                  Left factSpanExc -> case spanExcJustAfter factSpanExc of
                    Nothing -> Nothing -- Fact already covers up until Inf
                    Just factAfterT -> case ttspan of
                      DS_Point _ -> Nothing -- ttspan is a point, hence we cover it all.
                      DS_SpanExc tspan -> tspan `difference` LeftSpaceExc factAfterT
                in Just
                    ( T.empty
                    , -- For unknowns, simply split the derivation into the
                      -- unknown subspans.
                      concat
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
                      -- Split on chronological fact.
                      ++ fromKnowns (case factIsh of
                          Left noOccSpan -> T.singletonNoOcc tr (DS_SpanExc noOccSpan)
                          Right (t, NoOcc) -> T.singletonNoOcc tr (DS_Point t)
                          Right (t, Occ b) -> T.singletonOcc tr t b
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
              -- Assume there might be deadlock and derive chronologically. This
              -- will not delay the production of facts: with a PrevV
              -- dependency, we must solve chronologically (at least piecewise
              -- after known events occs).

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
          -- return the new VFact(s) and any new Derivation(s)
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
          -- Just Nothing: VFact found that goes to infinity
          -- Just (Just t): VFact found that ends at time t (exclusive)
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

      IfNoOccAt t deps der -> do
        mayKnownIsNoOccs <- forM deps $ \(SomeEIx depEIx) -> do
          mayKnownMayOcc <- lookupM t depEIx
          return $ case mayKnownMayOcc of
            Unknown -> Unknown
            Known mayOcc -> Known (Th.isNoOcc mayOcc)
        return $ case sequence mayKnownIsNoOccs of
          Unknown -> Nothing
          Known isNoOccs -> if and isNoOccs
            -- No dep events are occurring. Continue with the derivation.
            then Just (T.empty, [der])
            -- One or more dep events are occurring. Stop.
            else Just (T.empty, [])

    -- Append clearance fact if possible
    return $ case steppedMay of
      Nothing -> Nothing
      Just (vt, ders) -> Just
        ( FactsEl vt $ M.fromList
            [ let
              tLo = spanExcJustBefore tspan
              tHi = spanExcJustAfter tspan
              in (tLo, (tr, prevDeps, tHi))
              | Derivation tr (DS_SpanExc tspan) prevDeps (Pure _) _ <- ders
              , not (null prevDeps)
              ]
        , ders
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

instance Show DerivationDep where
  show dep = case dep of
    Dep_FactSpan ts eix -> "Dep_FactSpan " <> show ts <> " " <> show eix
    Dep_NegInf eix -> "Dep_NegInf " <> show eix
    Dep_JustBefore t eix -> "Dep_JustBefore " <> show t <> " " <> show eix
    Dep_JustAfter t eix -> "Dep_JustAfter " <> show t <> " " <> show eix
    Dep_DerivationClearance tmay eix -> "Dep_DerivationClearance " <> show tmay <> " " <> show eix

instance Pretty DerivationDep where
  pretty dep = case dep of
    Dep_FactSpan ts eix -> "Dep_FactSpan " <> pretty ts <> " " <> pretty eix
    Dep_NegInf eix -> "Dep_NegInf " <> pretty eix
    Dep_JustBefore t eix -> "Dep_JustBefore " <> pretty t <> " " <> pretty eix
    Dep_JustAfter t eix -> "Dep_JustAfter " <> pretty t <> " " <> pretty eix
    Dep_DerivationClearance tmay eix -> "Dep_DerivationClearance " <> pretty tmay <> " " <> pretty eix

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

lookupM
  :: Time
  -- ^ Time t too look up
  -> EIx a
  -> DerivationM (MaybeKnown (MaybeOcc a))
  -- ^ If known, Left is the NoOcc fact's time span spanning t and Right is the
  -- Occ or NoOcc point fact at time t.
lookupM t vix = do
  x <- lookupM' t vix
  return $ case x of
    Nothing -> Unknown
    Just (_, Left _) -> Known NoOcc
    Just (_, Right occMay) -> Known occMay

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

-- Note: Doesn't crop the returned SpanExc
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



instance Pretty KnowledgeBase where
  pretty kb = vsep
    [ "KnowledgeBase:"
    , indent 2 $ vsep $
      [ "kbFacts"          <+> pretty (kbFacts kb)
      , "kbDerivations"    <+> pretty (kbDerivations kb)
      , "kbHotDerivations" <+> pretty (kbHotDerivations kb)
      ]
    ]

instance Pretty Facts where
  pretty fs = nest 2 $ vsep $ "Facts" :
    [ nest 2 $ vsep
      [ pretty eix
      , hsep
        [ case eitherNoOccTsOrOcc of
            Left (DS_SpanExc s) -> pretty s
            Left (DS_Point t) -> "{NoOcc @" <> pretty t <> "}"
            Right (t, _) -> "{Occ @" <> pretty t <> "}"
        | (_, eitherNoOccTsOrOcc) <- T.elems tl
        ]
      ]
    | DM.SomeIx eix <- DM.keys fs
    , Just (FactsEl tl _) <- [DM.lookup eix fs]
    ]

instance Pretty (Set SomeDerivationID) where
  pretty s = encloseSep "{" "}" "," (pretty <$> S.toList s)

instance Pretty SomeDerivationID where
  pretty (SomeDerivationID eix did) = "SomeDerivationID" <+> pretty eix <+> pretty did

instance Pretty (DerivationID a) where
  pretty = fromString . show

instance Pretty DerivationsByDeps where
  pretty dbd = vsep
    [ "DerivationsByDeps:"
    , indent 2 $ vsep $
      [ "NextID" <+> pretty (dbdNextID dbd)
      , "Derivations" <+> pretty [ (DerivationID derId, eix, der) | (derId, (eix, der)) <- IM.assocs $ dbdDerivation dbd]
      , "DerivationDeps" <+> pretty (M.assocs $ dbdDerivationDeps dbd)
      , "IxSpanLoJurisdiction" <+> "_" -- pretty (dbdIxSpanLoJurisdiction dbd)
      , "IxDepOnFactSpan" <+> pretty (M.assocs $ dbdIxDepOnFactSpan dbd)
      , "IxDepOnNegInf" <+> "_" -- pretty (dbdIxDepOnNegInf dbd)
      , "IxDepOnJustBefore" <+> "_" -- pretty (dbdIxDepOnJustBefore dbd)
      , "IxDepOnJustAfter" <+> "_" -- pretty (dbdIxDepOnJustAfter dbd)
      , "IxDepOnDerivationClearance" <+> "_" -- pretty (dbdIxDepOnDerivationClearance dbd)
      ]
    ]
