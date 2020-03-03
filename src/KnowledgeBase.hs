{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wincomplete-uni-patterns #-}

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module KnowledgeBase where

import Data.List (foldl')
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (fromMaybe)

import KnowledgeBase.DMap (DMap)
import qualified KnowledgeBase.DMap as DMap
import KnowledgeBase.FactMap
import Time
import TimeSpan

data SourceEventDef a   = SourceEvent
data BehaviorDef game a = BehaviorDef [FactB a] (Rule game a)
data EventDef    game a = EventDef    [FactE a] (Rule game a)

newtype EIx a = EIx Int deriving (Eq, Ord, Show)
newtype BIx a = BIx Int deriving (Eq, Ord, Show)
data Ix a = Ix_B (BIx a) | Ix_E (EIx a)

class FieldIx game where
    fieldIxs :: game EIx EIx BIx

    eIx :: KeyE game a -> EIx a
    eIx k = k fieldIxs

    bIx :: KeyB game a -> BIx a
    bIx k = k fieldIxs

data CurrOrNext = Curr | Next
data Rule game a where
    DependencyE :: KeyE game a -> Rule game (Maybe a)
    DependencyB :: CurrOrNext -> KeyB game a -> Rule game a
    -- ^ Dependency on some other field in previous time or current time (CurrOrNext).
    Result :: a -> Rule game a
    Bind :: Rule game b -> (b -> Rule game a) -> Rule game a

-- If you define an Event in terms of a Rule, the meaning is simply to think of
-- it as a behaviour of (Occ a), sampled at all changes of the behaviour. So
-- this exposes the descrete nature of behaviours, but also alows us to express
-- things like "if your behaviour of Health == 0 then fire the Die event".

getB :: KeyB game a -> Rule game a
getB = DependencyB Curr

getNextB :: KeyB game a -> Rule game a
getNextB = DependencyB Next

getE :: KeyE game a -> Rule game (Maybe a)
getE = DependencyE

instance Functor (Rule game) where
    fmap f r = Bind r (pure . f)
instance Applicative (Rule game) where
    pure = Result
    ra2b <*> ra = do
        a2b <- ra2b
        a   <- ra
        return (a2b a)
instance Monad (Rule game) where
    (>>=) = Bind

--
-- Combinators
--

-- | For a single field, some initial facts (if any) and the corresponding rule.
foldB :: a -> Rule game a -> BehaviorDef game a
foldB aInit = BehaviorDef [(Init aInit)]

behavior :: Rule game a -> BehaviorDef game a
behavior = BehaviorDef []

{- IMPLEMENTATION NOTES

TODO PREFORMANCE

I'm worried about performance. Feels like there will be a lot of splitting of
the rules, resulting in a lot of recalculation even though the dependencies may
bot change.

-}

-- | All knowledge about all fields and meta-knowledge.
data KnowledgeBase game = KnowledgeBase
    { kbFactsE :: DMap EIx KBFactsE
    , kbFactsB :: DMap BIx KBFactsB
    -- ^ All known facts.
    , kbValuesB :: DMap BIx KBValuesB
    -- ^ The actual values for each time (no NoChange nonsense). Must reflect
    -- kbFactsB (though it may transitivelly omit some entries internally when
    -- updating the KnowledgeBase), but other than that, no invariants. Note
    -- that we don't need an equivalent field for Events, as that is exactly
    -- kbFactsE.
    , kbActiveRulesE :: DMap EIx (KbActiveRulesE game)
    , kbActiveRulesB :: DMap BIx (KbActiveRulesB game)
    -- ^ For each Field, f, a map from rule span start to rule spans and rule
    -- continuations. f is the rule's current dependency
    --
    -- All rules are initialized to their first dependency spanning all of
    -- time. Hence a rule will be fully discharged exactly once for all time,
    -- though will usually be split (potentially many times) into smaller spans.
    -- as facts are inserted.
    }

-- Facts contain either Change/NoChange facts, or solid values

data    KBValuesB a = KBValuesB (Maybe a) (Map TimeX (FactBCVal a))

newtype KbActiveRulesE game a = KbActiveRulesE                     (Map TimeX [ActiveRule game a])
data    KbActiveRulesB game a = KbActiveRulesB [ActiveRule game a] (Map TimeX [ActiveRule game a])
data ActiveRule game a
    = forall b . ActiveRule
        Bool
        -- ^ Has any of the deps so far actually indicated a change?
        (Either Time SpanExc)
        -- ^ result and dependencies span this time exactly.
        (Ix b)
        -- ^ result is for this field
        (a -> Rule game b)
        -- ^ Continuation


insertFacts :: FieldIx game
    => KnowledgeBase game
    -- ^ Current KnowledgeBase.
    -> [Fact game]
    -- ^ New Facts
    -> ( KnowledgeBase game
       -- ^ New KnowledgeBase.
       , [Fact game]
       -- ^ New derived facts (excluding the passed in new facts)
       )
insertFacts knowledgeBaseTop
    = foldl
        (\(kb, fs) f -> let (kb', fs') = insertFact f kb in (kb', fs' ++ fs))
        (knowledgeBaseTop, [])

insertFact :: forall game . FieldIx game
    => Fact game
    -- ^ A single fact to insert.
    -> KnowledgeBase game
    -- ^ Current KnowledgeBase.
    -> ( KnowledgeBase game
       -- ^ New KnowledgeBase.
       , [Fact game]
       -- ^ New derived facts (excluding the passed in new fact)
       )
insertFact fact kb@(KnowledgeBase currkbFactsE currkbFactsB currkbValuesB _ _)
    | overlaps = error $ "insertFacts: new fact overlaps existing facts" -- TODO better output

    -- 1. Directly insert the fact into the knowledge base.

    -- 2. If we've learned more about the actual value (due to step 1), update
    --    kbValuesB. There are only 2 cases where this happens (Init a) / (Change t
    --    Just _) is learned, or NoChanges is learned which neighbors known
    --    values in kbValuesB on the left (and possibly more NoChange values in
    --    kbFacts on the right)

    -- 3. With at most 1 possible update to either kbValuesB or to kbFactsE,
    --    look for overlapping active rules, split and evaluate them (actually
    --    removed and reinsert). This may lead to more active rules (you must
    --    insert recursively), and more facts that you must queue up to
    --    recursively insert.


    | otherwise = case fact of
        FactB (keyB :: KeyB game a) (factB :: FactB a) -> let

            ix :: BIx a
            ix = bIx keyB

            -- 1 Insert fact

            kbFactsB' :: DMap BIx KBFactsB
            kbFactsB' = DMap.alter
                (\mayFacts -> let
                    KBFactsB initVal cs = fromMaybe (KBFactsB Nothing Map.empty) mayFacts
                    in Just $ case factB of
                        Init a -> KBFactsB (Just a) cs
                        FactB_Change factBC@(Change t _)
                            -> KBFactsB initVal (Map.insert (toTime t) factBC cs)
                        FactB_Change factBC@(NoChange tspan)
                            -> KBFactsB initVal (Map.insert (spanExcMinT tspan) factBC cs)
                )
                ix
                currkbFactsB

            -- Is a concrete value known for this new fact's time (span)?
            knownValueMay :: Maybe a
            knownValueMay = case factB of
                Init a -> Just a
                FactB_Change (Change _ (Just a)) -> Just a
                -- If value is known just before t/tspan then insert that value at fact t/tspan and all right NoChange neighbors
                FactB_Change (Change t Nothing) -> lookupValueBJustBeforeTime    ix t     currkbValuesB
                FactB_Change (NoChange tspan)   -> lookupValueBJustBeforeSpanExc ix tspan currkbValuesB

            right = rightNoChangeNeighborsExc (kbFactsB' DMap.! ix) factB
            newValueFacts = maybe [] (\ a -> setValueForallFactB a <$> (factB : right)) knownValueMay

            -- 2 update kbValuesB
            -- Insert all the new value facts into the KnowledgeBase

            in foldl'
                (\(kb', fs) f -> let (kb'',fs') = insertValueFact ix f kb' in (kb'', fs' ++ fs))
                (kb { kbFactsB = kbFactsB' }, [])
                newValueFacts

        FactE keyE factCE -> let

            -- ix = eIx keyE

            -- -- 1 Insert fact

            -- kbFactsB = DMap.alter
            --     (\mayFacts -> let
            --         KBFactsE cs = fromMaybe (KBFactsE Map.empty) mayFacts
            --         in Just $ case factCE of
            --             FactOcc t _ -> KBFactsE (Map.insert (toTime t) factCE cs)
            --             FactNoOcc tspan -> KBFactsE (Map.insert (spanExcMinT tspan) factCE cs)
            --     )
            --     ix
            --     kbFactsE

            -- -- 3 Check `fact` against `kbActiveRules`, evaluate rules and recurs.

            in _ -- TODO will be similar to insertValueFact

    where

    -- | insert a value fact into the knowlege base. This will handle poking any
    -- active rules.
    insertValueFact
        :: BIx a
        -> FactBVal a
        -> KnowledgeBase game
        -> ( KnowledgeBase game
            -- ^ New KnowledgeBase.
            , [Fact game]
            -- ^ New derived facts (excluding the passed in new fact)
            )
    insertValueFact bix factBVal kb = let
        -- directly insert the value fact.
        KBValuesB oldAInit oldMap = fromMaybe (KBValuesB Nothing Map.empty)
                                              (DMap.lookup bix (kbValuesB kb))
        kbValuesB' = case factBVal of
            InitVal a -> KBValuesB (Just a) oldMap
            FactBVal_Change f@(ValueBChange t a)
                -> KBValuesB
                    oldAInit
                    (Map.insertWith
                        (error "insertValueFact: overlapping knowledge")
                        (toTime t)
                        f
                        oldMap
                    )
            FactBVal_Change f@(ValueBNoChange tSpan a)
                -> KBValuesB
                    oldAInit
                    (Map.insertWith
                        (error "insertValueFact: overlapping knowledge")
                        (spanExcMinT tSpan)
                        f
                        oldMap
                    )
        -- Find/remove all active rules who's time (span) intersects the value fact.

        -- Time span of the factBVal. Nothing means initial value.
        factBValSpan :: Maybe (Either Time SpanExc)
        factBValSpan = case factBVal of
            InitVal _ -> Nothing
            FactBVal_Change (ValueBChange t _)
                -> Just (Left t)
            FactBVal_Change (ValueBNoChange tSpan _)
                -> Just (Right tSpan)

        KbActiveRulesB oldARsInit oldARsMap
            = fromMaybe
                (KbActiveRulesB [] Map.empty)
                (DMap.lookup bix (kbActiveRulesB kb))

        (kbActiveRulesB', removedRules) = case factBValSpan of
            Nothing -> (KbActiveRulesB [] oldARsMap, oldARsInit)
            Just (Left t) -> case _ of
                _ -> _
            Just (Right tspan) -> _

        kb' = kb { kbActiveRulesB = DMap.alter (const (Just kbActiveRulesB')) bix (kbActiveRulesB kb) }

        -- Reinsert the active rules.
        in _

    -- | insert an active rule. The rule will be split into smaller spans and
    -- evaluated as far as possible.
    insertActiveRule
        :: Ix a
        -> ActiveRule game a
        -> KnowledgeBase game
        -> ( KnowledgeBase game
            -- ^ New KnowledgeBase.
            , [Fact game]
            -- ^ New derived facts.
            )
    insertActiveRule = _

    -- | Lookup the known value just before (i.e. neighboring) the given time.
    lookupValueBJustBeforeTime :: forall a . BIx a -> Time -> DMap BIx KBValuesB -> Maybe a
    lookupValueBJustBeforeTime ix t fm = do
        KBValuesB _ m <- DMap.lookup ix fm
        (_, factBCVal) <- Map.lookupLT (X_Exactly t) m
        case factBCVal of
            -- There is a unknown gap between current time, t, and the last
            -- ValueBChange, so return Nothing.
            ValueBChange _ _ -> Nothing
            ValueBNoChange tspan a -> if tspan `contains` X_JustBefore t
                then Just a
                else Nothing

    lookupValueBJustBeforeSpanExc :: forall a . BIx a -> SpanExc -> DMap BIx KBValuesB -> Maybe a
    lookupValueBJustBeforeSpanExc ix tspan fm = do
        KBValuesB initAMay m <- DMap.lookup ix fm
        case spanExcJustBefore tspan of
            Nothing -> initAMay
            Just tJustBefore -> do
                factBCVal <- Map.lookup (X_Exactly tJustBefore) m
                case factBCVal of
                    ValueBChange _ a -> Just a
                    -- We looked up an exact time, but ValueBNoChange's key must
                    -- be a X_JustAfter.
                    ValueBNoChange _ _ -> error "lookupValueBJustBeforeSpanExc: expected ValueBChange but found ValueBNoChange"

    -- Replace all facts with the given value.
    setValueForallFactB :: a -> FactB a -> FactBVal a
    setValueForallFactB a (Init _) = InitVal a
    setValueForallFactB a (FactB_Change (Change t _)) = FactBVal_Change (ValueBChange t a)
    setValueForallFactB a (FactB_Change (NoChange tspan)) = FactBVal_Change (ValueBNoChange tspan a)

    -- | Get all right NoChange neighbors (excludes input fact)
    rightNoChangeNeighborsExc
        :: KBFactsB a
        -> FactB a
        -- ^ Current fact. First neighbor start just after this fact.
        -> [FactB a]
    rightNoChangeNeighborsExc kBFactsB@(KBFactsB _ m) currFactB = case nextFactMay of
        Nothing -> []
        Just nextFact -> nextFact : rightNoChangeNeighborsExc kBFactsB nextFact
        where
        nextFactMay = case currFactB of
            Init a -> FactB_Change <$> Map.lookup X_NegInf m
            FactB_Change (Change t _)
                -> FactB_Change <$> Map.lookup (X_JustAfter t) m
            FactB_Change (NoChange tspan)
                -> do
                    -- If spanExcJustAfter gives Nothing then we've reached the
                    -- end of time, so can stop.
                    nextTx <- spanExcJustAfter tspan
                    FactB_Change <$> Map.lookup (X_Exactly nextTx) m




    overlaps :: Bool
    overlaps = _

