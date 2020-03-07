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

import Control.Applicative ((<|>))
import Control.Monad (forM, forM_, mapM_, when)
import Control.Monad.Trans.State.Lazy
import Data.List (find, foldl', group, takeWhile)
import Data.Maybe (fromMaybe)

import KnowledgeBase.DMap (DMap)
import qualified KnowledgeBase.DMap as DMap
import KnowledgeBase.Timeline hiding (insertFact)
import qualified KnowledgeBase.Timeline as T

import Time

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
    , kbActiveRulesE     :: DMap EIx (ActiveRules game)
    , kbActiveRulesBCurr :: DMap BIx (ActiveRules game)
    , kbActiveRulesBNext :: DMap BIx (ActiveRules game)
    -- ^ For each Field, f, a map from rule span start to rule spans and rule
    -- continuations. f is the rule's current dependency
    --
    -- All rules are initialized to their first dependency spanning all of
    -- time. Hence a rule will be fully discharged exactly once for all time,
    -- though will usually be split (potentially many times) into smaller spans.
    -- as facts are inserted.
    }

kbLookupB :: BIx a -> TimeX -> KnowledgeBase game -> Maybe a
kbLookupB bix tx kb = do
    let TimelineB timeline = kbFactsB kb DMap.! bix
    factBTx <- tlLookup tx timeline
    let leftNs = leftNeighbors timeline (toFactSpan factBTx)
    foldr (\fact valMay -> factBToMayVal fact <|> valMay) Nothing (factBTx : leftNs)


newtype ActiveRules game a = ActiveRules { unActiveRules :: MultiTimeline (ActiveRule game a) }
data ActiveRule game a
    = forall b . ActiveRuleB
        { ar_changeDetected :: Bool
        -- ^ Has any of the deps so far actually indicated a change?
        , ar_factSpan :: FactSpan
        -- ^ result and dependencies span this time exactly.
        , ar_finalFieldBIx :: BIx b
        -- ^ result is for this field
        , ar_continuationB :: a -> Rule game b
        -- ^ Continuation. Takes current dependencies value. Current dep is implicit.
        }
    | forall b . ActiveRuleE
        { ar_changeDetected :: Bool
        -- ^ Has any of the deps so far actually indicated a change?
        , ar_factSpan :: FactSpan
        -- ^ result and dependencies span this time exactly.
        , ar_finalFieldEIx :: EIx b
        -- ^ result is for this event
        , ar_continuationE :: a -> Rule game (Maybe b)
        -- ^ Continuation. Takes current dependencies value. Current dep is implicit.
        -- Nothing result means no event occurrence.
        }

data Fact game
    = forall a . FactB (BIx a) (FactB a)
    | forall a . FactE (EIx a) (FactE a)

-- | State is the KnowledgeBase and the facts learned (including initial facts).
type KnowledgeBaseM game = State (KnowledgeBase game, [Fact game])

writeFact :: Fact game -> KnowledgeBaseM game ()
writeFact fs' = modify (\(kb,fs) -> (kb, fs' : fs))

modifyKB :: (KnowledgeBase game -> KnowledgeBase game) -> KnowledgeBaseM game ()
modifyKB f = modify (\(kb,fs) -> (f kb, fs))

asksKB :: (KnowledgeBase game -> a) -> KnowledgeBaseM game a
asksKB f = gets (f . fst)

runKnowledgeBaseM_ :: KnowledgeBaseM game a -> KnowledgeBase game -> (KnowledgeBase game, [Fact game])
runKnowledgeBaseM_ m k = snd $ runState m (k, [])

insertFacts :: (FieldIx game)
    => KnowledgeBase game
    -- ^ Current KnowledgeBase.
    -> [Fact game]
    -- ^ New Facts
    -> ( KnowledgeBase game
       -- ^ New KnowledgeBase.
       , [Fact game]
       -- ^ New facts including the input facts.
       )
insertFacts knowledgeBaseTop fs
    = runKnowledgeBaseM_ (forM fs $ insertFact) knowledgeBaseTop

insertFact :: forall game . FieldIx game
    => Fact game
    -- ^ A single fact to insert.
    -> KnowledgeBaseM game ()
insertFact factTop = do
    overlaps <- _checkOverlap
    when overlaps $ error "insertFacts: new fact overlaps existing facts" -- TODO better output

    -- Store the new fact.
    writeFact factTop

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

    case factTop of
        FactB (ix :: BIx a) (factB :: FactB a) -> do

            -- 1 Directly insert fact.

            modifyKB $ \ kb -> kb
                { kbFactsB = DMap.update
                    (Just . TimelineB . T.insertFact factB . unTimelineB)
                    ix
                    (kbFactsB kb)
                }
            kbFactsB' <- asksKB kbFactsB

            -- From this we extrapolate forward what the curr/next values are
            -- in order to fire any active rules.

            -- The (current) value known just before the current fact's
            -- time span.
            currAMay :: Maybe a <- asksKB $
                kbLookupB ix (factSpanJustBeforeMinT (toFactSpan factB))

            -- The (next) value known for the current fact's time span.
            nextAMay :: Maybe a <- asksKB $
                kbLookupB ix (factSpanMinT (toFactSpan factB))

            let factBSpan = toFactSpan factB
                rightNs
                    = rightNeighbors
                        (unTimelineB $ kbFactsB' DMap.! ix)
                        (toFactSpan factB)
                fstRightChangeSpanMay = toFactSpan <$> find isChange rightNs
                rightNoChangeSpans
                    = fmap toFactSpan
                    $ takeWhile (not . isChange) rightNs

            forM_ currAMay $ \currA -> do
                -- For the current fact span we've learned the curr/next value.
                insertCurrValueFact ix currA factBSpan

                -- When factB is non-Change, the curr value is current value for
                -- right non-change neighbors.
                when (not (isChange factB)) $
                    mapM_ (insertCurrValueFact ix currA) rightNoChangeSpans
            forM_ nextAMay $ \nextA -> do
                -- For the current fact span we've learned the curr/next value.
                insertNextValueFact ix nextA factBSpan

                -- The next value is current value for right neighbors up to and
                -- including the first right value-change neighbor.
                mapM_ (insertCurrValueFact ix nextA) fstRightChangeSpanMay
                mapM_ (insertCurrValueFact ix nextA) rightNoChangeSpans

        FactE ix factE -> do

            -- 1 Directly insert fact.

            modifyKB $ \ kb -> kb
                { kbFactsE = DMap.update
                    (Just . TimelineE . T.insertFact factE . unTimelineE)
                    ix
                    (kbFactsE kb)
                }
            kbFactsB' <- asksKB kbFactsB

            -- kbFactsE'
            --     = DMap.update
            --         (Just . TimelineE . T.insertFact factE . unTimelineE)
            --         ix
            --         currkbFactsE

            -- (intersectingActiveRules, activeRulesMT')
            --     = cropView
            --         (unActiveRules $ kbActiveRulesE kbTop DMap.! ix)
            --         (toFactSpan factE)

            -- -- -- 3 Check `fact` against `kbActiveRules`, evaluate rules and recurs.

            -- in _ kbFactsE' intersectingActiveRules activeRulesMT'-- TODO will be similar to insertValueFact
            _

    where
    insertCurrValueFact
        :: BIx a
        -> a
        -> FactSpan
        -> KnowledgeBaseM game ()
    insertCurrValueFact
        = insertValueFact
            kbActiveRulesBCurr
            (\kb activeRules -> kb { kbActiveRulesBCurr = activeRules })

    -- | insert a value fact into the knowlege base. This will handle poking any
    -- active rules.
    insertNextValueFact
        :: BIx a
        -> a
        -> FactSpan
        -> KnowledgeBaseM game ()
    insertNextValueFact
        = insertValueFact
            kbActiveRulesBNext
            (\kb activeRules -> kb { kbActiveRulesBNext = activeRules })

    insertValueFact
        :: (KnowledgeBase game -> DMap BIx (ActiveRules game))
        -- ^ Get current or next active rules.
        -> (KnowledgeBase game -> DMap BIx (ActiveRules game) -> KnowledgeBase game)
        -- ^ Set current or next active rules.
        -> BIx a
        -> a
        -> FactSpan
        -> KnowledgeBaseM game ()
    insertValueFact getActiveRules setActiveRules bix a valueFactSpan = do
        -- Find/remove all active rules who's time (span) intersects the value fact.
        ActiveRules activeRulesMT <- asksKB $ \kb -> (getActiveRules kb) DMap.! bix
        let (extractedActiveRules, activeRulesMT') = cropView activeRulesMT valueFactSpan
        modifyKB $ \kb -> setActiveRules kb (DMap.update (const $ Just $ ActiveRules activeRulesMT') bix (getActiveRules kb))

        -- Step all the extracted active rules and reinsert them either as new
        -- active rules, or as facts (if the rule terminates).
        forM_ extractedActiveRules $ \activeRule -> case activeRule of
            ActiveRuleB _changeDetected factSpan finalFieldBIx continuationB ->
                -- TODO use changeDetected
                case continuationB a of
                    Result r -> insertFact (FactB finalFieldBIx (case factSpan of
                        FS_Init -> Init r
                        FS_Point t -> ChangePoint t (MaybeChange (Just r))   -- TODO allow Rule to return "NoChange" for behaviours
                        FS_Span tspan -> ChangeSpan tspan NoChange
                        ))
                    DependencyE keyE cont -> _insertActiveRuleE (eIx keyE)
                        -- TODO detect change correctly instead of using False.
                        (ActiveRuleB False factSpan finalFieldBIx cont)
                    DependencyB con keyB cont -> _insertActiveRuleB con (bIx keyB)
                        -- TODO detect change correctly instead of using False.
                        (ActiveRuleB False factSpan finalFieldBIx cont)
            ActiveRuleE _changeDetected factSpan finalFieldEIx continuationE ->
                case continuationE a of
                    Result r -> insertFact (FactE finalFieldEIx (case factSpan of
                        FS_Init -> error "Trying to set Init value of an Event but events don't have initial values. Did you accidentally insert a Rule for an event that spans all of time including the initial value?"
                        FS_Point t -> ChangePoint t r
                        FS_Span tspan -> ChangeSpan tspan NoChange
                        ))
                    DependencyE keyE cont -> _insertActiveRuleE (eIx keyE)
                        -- TODO detect change correctly instead of using False.
                        (ActiveRuleE False factSpan finalFieldEIx cont)
                    DependencyB con keyB cont -> _insertE con (bIx keyB)
                        -- TODO detect change correctly instead of using False.
                        (ActiveRuleE False factSpan finalFieldEIx cont)

        -- mapM_ (insertActiveRuleB getActiveRules setActiveRules bix a) extractedActiveRules

    -- | insert an active rule. The rule will be split into smaller spans and
    -- evaluated as far as possible.
    -- insertActiveRule
    --     :: ActiveRule game a
    --     -> KnowledgeBaseM game ()
    -- insertActiveRule getActiveRules setActiveRules bix activeRule = _
        -- TODO check for overlapping insertion
    -- insertActiveRule
    --   ix
    --   activeRule
    --   kb
    --   = case ix of
    --     Ix_B (bix :: BIx a) -> let
    --         depVals :: [FactBVal a]
    --         depVals = _crop (unTimelineBVal (kbValuesB kb DMap.! bix)) (ar_factSpan activeRule)
    --         in foldl'
    --             (\(kb', fs) depVal -> let
    --                 a = factBValToVal depVal
    --                 -- Run the rule
    --                 (kb'', fs') = case activeRule of
    --                     ActiveRuleB _arChangeDetected arFactSpan arFinalBIx arContinuation
    --                         -> case arContinuation a of
    --                             -- Got a result, so insert the newly learned fact
    --                             Result r -> insertFact
    --                                 (FactB arFinalBIx (case arFactSpan of
    --                                     FS_Init -> Init r
    --                                     -- TODO make use of arChangeDetected: if no
    --                                     -- change detected, the resulting fact
    --                                     -- should be NoChange
    --                                     FS_Point t -> ChangePoint t (MaybeChange (Just r))
    --                                     FS_Span tspan -> ChangeSpan tspan NoChange
    --                                     )
    --                                 )
    --                                 kb'
    --                             -- Got a new active rule. Insert it.
    --                             DependencyE ke cont -> _
    --                             DependencyB _ ke cont -> _
    --                             -- Left (nextDepIx', activeRule') -> insertActiveRule nextDepIx' activeRule' kb'
    --                     ActiveRuleE _arChangeDetected arFactSpan arFinalEIx arContinuation
    --                         -> case arContinuation a of
    --                             -- -- Got a result, so insert the newly learned fact
    --                             -- Result r -> insertFact
    --                             --     (FactB arFinalBIx (case arFactSpan of
    --                             --         FS_Init -> Init r
    --                             --         -- TODO make use of arChangeDetected: if no
    --                             --         -- change detected, the resulting fact
    --                             --         -- should be NoChange
    --                             --         FS_Point t -> ChangePoint t (MaybeChange (Just r))
    --                             --         FS_Span tspan -> ChangeSpan tspan NoChange
    --                             --         )
    --                             --     )
    --                             --     kb'
    --                             _ -> _
    --                                     -- Ix_E rEix -> FactE rEix <$> (case arFactSpan of
    --                                     --     FS_Init -> Nothing
    --                                     --     -- TODO make use of arChangeDetected: if no
    --                                     --     -- change detected, the resulting fact
    --                                     --     -- should be NoChange
    --                                     --     FS_Point t -> Just $ ChangePoint t (Just r)
    --                                     --     FS_Span tspan -> Just $ ChangeSpan tspan NoChange
    --                                     --     )
    --                 in (kb'', fs' ++ fs)
    --             )
    --             (kb, [])
    --             depVals
    --     Ix_E eix -> _

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
