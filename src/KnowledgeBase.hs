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

import Data.List (foldl', takeWhile)
import Data.Maybe (fromMaybe)

import KnowledgeBase.DMap (DMap)
import qualified KnowledgeBase.DMap as DMap
import KnowledgeBase.Timeline hiding (insertFact)
import qualified KnowledgeBase.Timeline as T

data SourceEventDef a   = SourceEvent
data BehaviorDef game a = BehaviorDef [FactB a] (Rule game a)
data EventDef    game a = EventDef    [FactE a] (Rule game a)

newtype EIx a = EIx Int deriving (Eq, Ord, Show)
newtype BIx a = BIx Int deriving (Eq, Ord, Show)
data Ix a = Ix_B (BIx a) | Ix_E (EIx a)

type KeyB game a = forall e b . game e e b -> b a
type KeyE game a = forall e b . game e e b -> e a
data Key game a
    = KeyB (KeyB game a)
    | KeyE (KeyE game a)

class FieldIx game where
    fieldIxs :: game EIx EIx BIx

    eIx :: KeyE game a -> EIx a
    eIx k = k fieldIxs

    bIx :: KeyB game a -> BIx a
    bIx k = k fieldIxs

data CurrOrNext = Curr | Next

-- TODO change to church encoding
data Rule game a where
    DependencyE :: KeyE game b -> (Maybe b -> Rule game a) -> Rule game a
    DependencyB :: CurrOrNext -> KeyB game b -> (b -> Rule game a) -> Rule game a
    -- ^ Dependency on some other field in previous time or current time (CurrOrNext).
    Result :: a -> Rule game a

-- If you define an Event in terms of a Rule, the meaning is simply to think of
-- it as a behaviour of (Occ a), sampled at all changes of the behaviour. So
-- this exposes the descrete nature of behaviours, but also alows us to express
-- things like "if your behaviour of Health == 0 then fire the Die event".

getB :: KeyB game a -> Rule game a
getB k = DependencyB Curr k Result

getNextB :: KeyB game a -> Rule game a
getNextB k = DependencyB Next k Result

getE :: KeyE game a -> Rule game (Maybe a)
getE k = DependencyE k Result

instance Functor (Rule game) where
    fmap f (DependencyE k cont) = DependencyE k (fmap f <$> cont)
    fmap f (DependencyB con k cont) = DependencyB con k (fmap f <$> cont)
    fmap f (Result a) = Result (f a)
instance Applicative (Rule game) where
    pure = Result
    ra2b <*> ra = do
        a2b <- ra2b
        a2b <$> ra
instance Monad (Rule game) where
    ruleA >>= cont = join $ fmap cont ruleA
        where
        join :: (Rule game (Rule game a)) -> Rule game a
        join (Result r) = r
        join (DependencyE k cont') = DependencyE k (fmap join cont')
        join (DependencyB con k cont') = DependencyB con k (fmap join cont')

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
    { kbFactsE :: DMap EIx TimelineE
    , kbFactsB :: DMap BIx TimelineB
    -- ^ All known facts.
    , kbValuesB :: DMap BIx TimelineBVal
    -- ^ The actual values for each time (no NoChange nonsense). Must reflect
    -- kbFactsB (though it may transitivelly omit some entries internally when
    -- updating the KnowledgeBase), but other than that, no invariants. Note
    -- that we don't need an equivalent field for Events, as that is exactly
    -- kbFactsE.
    , kbActiveRulesE :: DMap EIx (ActiveRules game)
    , kbActiveRulesB :: DMap BIx (ActiveRules game)
    -- ^ For each Field, f, a map from rule span start to rule spans and rule
    -- continuations. f is the rule's current dependency
    --
    -- All rules are initialized to their first dependency spanning all of
    -- time. Hence a rule will be fully discharged exactly once for all time,
    -- though will usually be split (potentially many times) into smaller spans.
    -- as facts are inserted.
    }

newtype ActiveRules game a = ActiveRules { unActiveRules :: MultiTimeline (ActiveRule game a) }
data ActiveRule game a
    = forall b . ActiveRuleB
        { ar_changeDetected :: Bool
        -- ^ Has any of the deps so far actually indicated a change?
        , ar_factSpan :: FactSpan
        -- ^ result and dependencies span this time exactly.
        , ar_finalFieldEIx :: BIx b
        -- ^ result is for this field
        , ar_continuationB :: a -> Rule game b
        -- ^ Continuation. Takes current dependencies value. Current dep is implicit.
        }
    | forall b . ActiveRuleE
        { ar_changeDetected :: Bool
        -- ^ Has any of the deps so far actually indicated a change?
        , ar_factSpan :: FactSpan
        -- ^ result and dependencies span this time exactly.
        , ar_finalFieldBIx :: EIx b
        -- ^ result is for this event
        , ar_continuationE :: a -> Rule game (Maybe b)
        -- ^ Continuation. Takes current dependencies value. Current dep is implicit.
        -- Nothing result means no event occurrence.
        }

data Fact game
    = forall a . FactB (BIx a) (FactB a)
    | forall a . FactE (EIx a) (FactE a)

insertFacts :: (FieldIx game)
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
insertFact fact kbTop@(KnowledgeBase currkbFactsE currkbFactsB currkbValuesB _ _)
    | overlaps = error $ "insertFacts: new fact overlaps existing facts" -- TODO better output

    -- 1. Directly insert the fact into the knowledge base.

    -- 2. If we've learned more about the actual value (due to step 1), update
    --    kbValuesB. There are only 2 cases where this happens (FB_Init a) / (FBC_Change t
    --    Just _) is learned, or NoChanges is learned which neighbors known
    --    values in kbValuesB on the left (and possibly more NoChange values in
    --    kbFacts on the right)

    -- 3. With at most 1 possible update to either kbValuesB or to kbFactsE,
    --    look for overlapping active rules, split and evaluate them (actually
    --    removed and reinsert). This may lead to more active rules (you must
    --    insert recursively), and more facts that you must queue up to
    --    recursively insert.


    | otherwise = case fact of
        FactB (ix :: BIx a) (factB :: FactB a) -> let

            -- 1 Insert fact

            kbFactsB' :: DMap BIx TimelineB
            kbFactsB'
                = DMap.update
                    (Just . TimelineB . T.insertFact factB . unTimelineB)
                    ix
                    currkbFactsB

            -- Is a concrete value known for this new fact's time (span)?
            knownValueMay :: Maybe a
            knownValueMay = case leftNeighbors (unTimelineBVal $ currkbValuesB DMap.! ix) (toFactSpan factB) of
                [] -> Nothing
                (a:_) -> Just (factBValToVal a)

            -- 2 update kbValuesB
            -- Insert all the new value facts into the KnowledgeBase

            right = takeWhile (not . isChange) (rightNeighbors (unTimelineB $ kbFactsB' DMap.! ix) (toFactSpan factB))
            newValueFacts = maybe [] (\ a -> setValueForallFactB a <$> (factB : right)) knownValueMay
            in foldl'
                (\(kb', fs) f -> let (kb'',fs') = insertValueFact ix f kb' in (kb'', fs' ++ fs))
                (kbTop { kbFactsB = kbFactsB' }, [])
                newValueFacts

        FactE ix factE -> let

            -- -- 1 Insert fact

            kbFactsE'
                = DMap.update
                    (Just . TimelineE . T.insertFact factE . unTimelineE)
                    ix
                    currkbFactsE

            (intersectingActiveRules, activeRulesMT')
                = cropView
                    (unActiveRules $ kbActiveRulesE kbTop DMap.! ix)
                    (toFactSpan factE)

            -- -- 3 Check `fact` against `kbActiveRules`, evaluate rules and recurs.

            in _ kbFactsE' intersectingActiveRules activeRulesMT'-- TODO will be similar to insertValueFact

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
        kbValuesB'
            = DMap.update
                (Just . TimelineBVal . T.insertFact factBVal . unTimelineBVal)
                bix
                (kbValuesB kb)

        -- Find/remove all active rules who's time (span) intersects the value fact.
        (ActiveRules activeRulesMT) = kbActiveRulesB kb DMap.! bix
        (intersectingActiveRules, activeRulesMT')
            = cropView activeRulesMT (toFactSpan factBVal)

        kb' = kb { kbValuesB = kbValuesB'
                 , kbActiveRulesB = DMap.update
                    (Just . ActiveRules . const activeRulesMT')
                    bix
                    (kbActiveRulesB kb)
                 }

        -- Reinsert the active rules.
        in foldl'
                (\(kb'2, fs) f -> let (kb'3,fs') = insertActiveRule (Ix_B bix) f kb'2 in (kb'3, fs' ++ fs))
                (kb', [])
                intersectingActiveRules

    -- | insert an active rule. The rule will be split into smaller spans and
    -- evaluated as far as possible.
    insertActiveRule
        :: Ix a
        -- ^ Ix of active rule's next dependency
        -> ActiveRule game a
        -> KnowledgeBase game
        -> ( KnowledgeBase game
            -- ^ New KnowledgeBase.
            , [Fact game]
            -- ^ New derived facts.
            )
    insertActiveRule
      ix
      activeRule
      kb
      = case ix of
        Ix_B (bix :: BIx a) -> let
            depVals :: [FactBVal a]
            depVals = _crop (unTimelineBVal (kbValuesB kb DMap.! bix)) (ar_factSpan activeRule)
            in foldl'
                (\(kb', fs) depVal -> let
                    a = factBValToVal depVal
                    -- Run the rule
                    (kb'', fs') = case activeRule of
                        ActiveRuleB _arChangeDetected arFactSpan arFinalBIx arContinuation
                            -> case arContinuation a of
                                -- Got a result, so insert the newly learned fact
                                Result r -> insertFact
                                    (FactB arFinalBIx (case arFactSpan of
                                        FS_Init -> Init r
                                        -- TODO make use of arChangeDetected: if no
                                        -- change detected, the resulting fact
                                        -- should be NoChange
                                        FS_Point t -> ChangePoint t (MaybeChange (Just r))
                                        FS_Span tspan -> ChangeSpan tspan NoChange
                                        )
                                    )
                                    kb'
                                -- Got a new active rule. Insert it.
                                Left (nextDepIx', activeRule') -> insertActiveRule nextDepIx' activeRule' kb'
                        ActiveRuleE _arChangeDetected arFactSpan arFinalEIx arContinuation
                            -> case arContinuation a of
                                -- Got a result, so insert the newly learned fact
                                Result r -> insertFact
                                    (FactB arFinalBIx (case arFactSpan of
                                        FS_Init -> Init r
                                        -- TODO make use of arChangeDetected: if no
                                        -- change detected, the resulting fact
                                        -- should be NoChange
                                        FS_Point t -> ChangePoint t (MaybeChange (Just r))
                                        FS_Span tspan -> ChangeSpan tspan NoChange
                                        )
                                    )
                                    kb'
                                _ -> _
                                        -- Ix_E rEix -> FactE rEix <$> (case arFactSpan of
                                        --     FS_Init -> Nothing
                                        --     -- TODO make use of arChangeDetected: if no
                                        --     -- change detected, the resulting fact
                                        --     -- should be NoChange
                                        --     FS_Point t -> Just $ ChangePoint t (Just r)
                                        --     FS_Span tspan -> Just $ ChangeSpan tspan NoChange
                                        --     )
                    in (kb'', fs' ++ fs)
                )
                (kb, [])
                depVals
        Ix_E eix -> _

        --

    -- -- | Lookup the known value just before (i.e. neighboring) the given time.
    -- lookupValueBJustBeforeTime :: forall a . BIx a -> Time -> DMap BIx TimelineBVal -> Maybe a
    -- lookupValueBJustBeforeTime ix t fm = case leftNeighbors t () do
    --     TimelineBVal _ m <- fm DMap.! ix
    --     (_, factBCVal) <- Map.lookupLT (X_Exactly t) m
    --     case factBCVal of
    --         -- There is a unknown gap between current time, t, and the last
    --         -- FBCV_Change, so return Nothing.
    --         FBCV_Change _ _ -> Nothing
    --         FBCV_NoChange tspan a -> if tspan `contains` X_JustBefore t
    --             then Just a
    --             else Nothing

    -- lookupValueBJustBeforeSpanExc :: forall a . BIx a -> SpanExc -> DMap BIx TimelineBVal -> Maybe a
    -- lookupValueBJustBeforeSpanExc ix tspan fm = do
    --     TimelineBVal initAMay m <- fm DMap.! ix
    --     case spanExcJustBefore tspan of
    --         Nothing -> initAMay
    --         Just tJustBefore -> do
    --             factBCVal <- Map.lookup (X_Exactly tJustBefore) m
    --             case factBCVal of
    --                 FBCV_Change _ a -> Just a
    --                 -- We looked up an exact time, but FBCV_NoChange's key must
    --                 -- be a X_JustAfter.
    --                 FBCV_NoChange _ _ -> error "lookupValueBJustBeforeSpanExc: expected FBCV_Change but found FBCV_NoChange"

    -- -- | Get all right NoChange neighbors (excludes input fact)
    -- rightNoChangeNeighborsExc
    --     :: TimelineB a
    --     -> FactB a
    --     -- ^ Current fact. First neighbor start just after this fact.
    --     -> [FactB a]
    -- rightNoChangeNeighborsExc kBFactsB@(TimelineB _ m) currFactB = case nextFactMay of
    --     Nothing -> []
    --     Just nextFact -> nextFact : rightNoChangeNeighborsExc kBFactsB nextFact
    --     where
    --     nextFactMay = case currFactB of
    --         FB_Init a -> FB_Change <$> Map.lookup X_NegInf m
    --         FB_Change (FBC_Change t _)
    --             -> FB_Change <$> Map.lookup (X_JustAfter t) m
    --         FB_Change (FBC_NoChange tspan)
    --             -> do
    --                 -- If spanExcJustAfter gives Nothing then we've reached the
    --                 -- end of time, so can stop.
    --                 nextTx <- spanExcJustAfter tspan
    --                 FB_Change <$> Map.lookup (X_Exactly nextTx) m




    overlaps :: Bool
    overlaps = _

