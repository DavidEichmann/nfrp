{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module KnowledgeBase
    ( -- Language Definition
      GameData (..)
    , FieldType (..)
    , KeyB
    , KeyE
    , KeySE
    , FieldIx (..)
    , B, SE, E

    , Rule
    , sourceEventDef
    , foldB
    , behavior
    , event
    , getB
    , getNextB
    , getE

    -- Knowledge base management
    , KnowledgeBase
    , newKnowledgeBase
    , insertFacts
    , lookupB
    , lookupE

    -- Facts
    , Fact
    , facts
    , factNoChangeSpanE
    ) where


import Control.Applicative ((<|>))
import Control.Monad (forM, forM_, mapM_, when)
import Control.Monad.Trans.State.Lazy
import Data.Kind
import Data.List (find, nub, sort, takeWhile)
import Data.Maybe (fromMaybe)
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.String
import Generics.SOP

import KnowledgeBase.DMap (DMap)
import qualified KnowledgeBase.DMap as DMap
import KnowledgeBase.Timeline hiding (insertFact)
import qualified KnowledgeBase.Timeline as T

import TimeSpan
import Time

--
-- FRP surface language (This shouled be moved to FRP module)
--

data SourceEventDef a   = SourceEventDef
sourceEventDef :: Field game 'SourceEvent 'Definition a
sourceEventDef = Field SourceEventDef
data BehaviorDef (game :: GameData -> Type) a = BehaviorDef [FactB a] (Rule game a)
data EventDef    (game :: GameData -> Type) a = EventDef    [FactE a] (Rule game (Maybe a))

data CurrOrNext = Curr | Next

-- TODO change to church encoding
data Rule (game :: GameData -> Type) a where
    DependencyE :: EIx b -> (Maybe b -> Rule game a) -> Rule game a
    DependencyB :: CurrOrNext -> BIx b -> (b -> Rule game a) -> Rule game a
    -- ^ Dependency on some other field in previous time or current time (CurrOrNext).
    Result :: a -> Rule game a

-- If you define an Event in terms of a Rule, the meaning is simply to think of
-- it as a behaviour of (Occ a), sampled at all changes of the behaviour. So
-- this exposes the descrete nature of behaviours, but also alows us to express
-- things like "if your behaviour of Health == 0 then fire the Die event".

getB :: FieldIx game => KeyB game a -> Rule game a
getB k = DependencyB Curr (bIx k) Result

getNextB :: FieldIx game => KeyB game a -> Rule game a
getNextB k = DependencyB Next (bIx k) Result

getE :: (FieldIx game, F game eventType 'Index a ~ EIx a)
    => (game 'Index -> Field game eventType 'Index a)
    -> Rule game (Maybe a)
getE k = DependencyE (eIx k) Result

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
foldB :: a -> Rule game a -> Field game 'Behavior 'Definition a
foldB aInit r = Field $ BehaviorDef [(Init aInit)] r

behavior :: Rule game a -> Field game 'Behavior 'Definition a
behavior r = Field $ BehaviorDef [] r

event :: Rule game (Maybe a) -> Field game 'Event 'Definition a
event r = Field $ EventDef [] r

{-

TODO PREFORMANCE

I'm worried about performance. Feels like there will be a lot of splitting of
the rules. In particular I'm worried that we recalculate even though values have
not changed.

We may spend too much time in lookupBIx traversing backwards to find the latest
change. One solution would be to add an invariant on kbFactsB that all runs of
NoChange must be combined into a single NoChange span where possible. This might
just be a simple change to `insertFact`.

-}

-- | All knowledge about all fields and meta-knowledge.
data KnowledgeBase game = KnowledgeBase
    { kbFactsE :: DMap EIx TimelineE
    , kbFactsB :: DMap BIx TimelineB
    -- ^ All known facts.
    , kbActiveRulesE     :: DMap EIx (ActiveRulesE game)
    , kbActiveRulesBCurr :: DMap BIx (ActiveRulesB game)
    , kbActiveRulesBNext :: DMap BIx (ActiveRulesB game)
    -- ^ Key (EIx/BIx), k, is the active rules' current dependency.
    --
    -- All rules are initialized to their first dependency spanning all of time
    -- (except events' rules don't cover initial value). Hence a rule will be
    -- fully discharged exactly once for all time, though will usually be split
    -- (potentially many times) into smaller spans. as facts are inserted.
    }

lookupBIx :: BIx a -> TimeX -> KnowledgeBase game -> Maybe a
lookupBIx bix tx kb = do
    let TimelineB timeline = kbFactsB kb DMap.! bix
    factBTx <- tlLookup tx timeline
    let leftNs = leftNeighbors timeline (toFactSpan factBTx)
    foldr (\fact valMay -> factBToMayVal fact <|> valMay) Nothing (factBTx : leftNs)

lookupB :: FieldIx game => KeyB game a -> TimeX -> KnowledgeBase game -> Maybe a
lookupB keyb = lookupBIx (bIx keyb)

lookupEIx :: EIx a -> Time -> KnowledgeBase game -> Maybe (Maybe a)
lookupEIx eix t kb = do
    let TimelineE timeline = kbFactsE kb DMap.! eix
    f <- tlLookup (toTime t) timeline
    case f of
        Init _ -> error "lookupEIx: found Init event"
        ChangePoint _ e -> Just e
        ChangeSpan _ NoChange  -> Just Nothing

lookupE :: (F game eventType 'Index a ~ EIx a, FieldIx game)
    => (game 'Index -> Field game eventType 'Index a)
    -> Time
    -> KnowledgeBase game
    -> Maybe (Maybe a)
lookupE keyb = lookupEIx (eIx keyb)


newtype ActiveRulesB game a = ActiveRulesB { unActiveRulesB :: MultiTimeline (ActiveRule game a) }
newtype ActiveRulesE game a = ActiveRulesE { unActiveRulesE :: MultiTimeline (ActiveRule game (Maybe a)) }
data ActiveRule game a
    = forall b . ActiveRuleB
        { ar_factSpan :: FactSpan
        -- ^ result and dependencies span this time exactly.
        , _ar_finalFieldBIx :: BIx b
        -- ^ result is for this field
        , _ar_continuationB :: a -> Rule game b
        -- ^ Continuation. Takes current dependencies value. Current dep is implicit.
        }
    | forall b . ActiveRuleE
        { ar_factSpan :: FactSpan
        -- ^ result and dependencies span this time exactly.
        , _ar_finalFieldEIx :: EIx b
        -- ^ result is for this event
        , _ar_continuationE :: a -> Rule game (Maybe b)
        -- ^ Continuation. Takes current dependencies value. Current dep is implicit.
        -- Nothing result means no event occurrence.
        }

instance CropView (ActiveRule game a) FactSpan [ActiveRule game a] [ActiveRule game a] where
    cropView activeRule factSpan = case ar_factSpan activeRule `intersect` factSpan of
      Nothing -> ([], [activeRule])
      Just cropSpan ->
        let outsideSpans :: [FactSpan]
            outsideSpans = ar_factSpan activeRule `difference` factSpan

            outsideActiveRules :: [ActiveRule game a]
            outsideActiveRules = case activeRule of
                ActiveRuleB _ finalBix cont
                    -> [ ActiveRuleB s finalBix cont | s <- outsideSpans ]
                ActiveRuleE _ finalEix cont
                    -> [ ActiveRuleE s finalEix cont | s <- outsideSpans ]

            -- THEN continue and insert the covered active rules
            insideActiveRule :: ActiveRule game a
            insideActiveRule = case activeRule of
                ActiveRuleB _ finalBix cont
                    -> ActiveRuleB cropSpan finalBix cont
                ActiveRuleE _ finalEix cont
                    -> ActiveRuleE cropSpan finalEix cont
        in ([insideActiveRule], outsideActiveRules)

data Fact game
    = forall a . FactB (BIx a) (FactB a)
    | forall a . FactE (EIx a) (FactE a)

-- | Create some facts about a source event.
facts :: FieldIx game
      => KeySE game a
      -> Maybe Time
      -- ^ Start of known time span (Exclusive). Nothing means negative infinity.
      -> Maybe Time
      -- ^ End of known time span (Inclusive). Nothing means positive infinity.
      -> [(Time, a)]
      -- ^ Event occurences. Must be strictly increasing in time and all in the
      -- given known time span.
      -> [Fact game]
      -- The resulting facts.
facts keySE tLoMayTop tHiMay occs = case outOfRangeOccs of
    (_:_) -> error $ "facts: input occurrences are out of the range " ++ show tspan ++ ": " ++ show occTs
    _ | occTs == sort (nub occTs) -> FactE eix <$> go tLoMayTop occs
      | otherwise -> error $ "facts: input occurrences times are not strictly increasing: " ++ show occTs
    where
    occTs = fst <$> occs
    tspan = spanExcInc tLoMayTop tHiMay
    outOfRangeOccs = filter (not . contains tspan . fst) occs
    eix = eIx keySE

    go loMay []
        | Just tHi <- tHiMay
        = if loMay == tHiMay
            then []
            else ChangeSpan (spanExc loMay tHiMay) NoChange
                    : [ChangePoint tHi Nothing]
        | otherwise = [ChangeSpan (spanExc loMay tHiMay) NoChange]
    go loMay ((t,a):as)
        = ChangeSpan (spanExc loMay (Just t)) NoChange
            : ChangePoint t (Just a)
            : go (Just t) as

-- | Create a fact for a span of time (exclusive) where no events occur for a source event.
factNoChangeSpanE :: forall game (a :: Type) . FieldIx game
    => KeySE game a
    -> Maybe Time
    -- ^ Start of known time span (Exclusive). Nothing means negative infinity.
    -> Maybe Time
    -- ^ End of known time span (Exclusive). Nothing means positive infinity.
    -> Fact game
factNoChangeSpanE keySE loT hiT = FactE (eIx keySE) (ChangeSpan (spanExc loT hiT) NoChange :: FactE a)

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

newKnowledgeBase :: FieldIx game => game 'Definition -> KnowledgeBase game
newKnowledgeBase gameDef = let
    emptyKB = KnowledgeBase
        { kbFactsE = DMap.empty (TimelineE T.empty) :: DMap EIx TimelineE
        , kbFactsB = DMap.empty (TimelineB T.empty) :: DMap BIx TimelineB
        -- ^ All known facts.
        , kbActiveRulesE     = DMap.empty (ActiveRulesE mtEmpty) :: DMap EIx (ActiveRulesE game)
        , kbActiveRulesBCurr = DMap.empty (ActiveRulesB mtEmpty) :: DMap BIx (ActiveRulesB game)
        , kbActiveRulesBNext = DMap.empty (ActiveRulesB mtEmpty) :: DMap BIx (ActiveRulesB game)
        -- All rules are initialized to their first dependency spanning all of time
        -- (except events' rules don't cover initial value). Hence a rule will be
        -- fully discharged exactly once for all time, though will usually be split
        -- (potentially many times) into smaller spans. as facts are inserted.
        }
    initializeKB = sequence_ $ traverseFields gameDef
        (\_ (Field SourceEventDef) -> return ())
        (\eix (Field (EventDef fs rule)) -> do
                mapM_ insertFact (FactE eix <$> fs)
                insertRuleE eix rule
        )
        (\bix (Field (BehaviorDef fs rule)) -> do
            mapM_ insertFact (FactB bix <$> fs)
            insertRuleB bix rule
        )

    in fst $ runKnowledgeBaseM_ initializeKB emptyKB


insertFacts :: (FieldIx game)
    => [Fact game]
    -- ^ New Facts
    -> KnowledgeBase game
    -- ^ Current KnowledgeBase.
    -> KnowledgeBase game
    -- ^ New KnowledgeBase.
insertFacts fs knowledgeBaseTop
    = fst $ runKnowledgeBaseM_ (forM fs $ insertFact) knowledgeBaseTop

insertFact :: forall game . FieldIx game
    => Fact game
    -- ^ A single fact to insert.
    -> KnowledgeBaseM game ()
insertFact factTop = do
    () <- asksKB $ \kb -> case factTop of
        FactB ix f -> case fst (cropView (unTimelineB (kbFactsB kb DMap.! ix)) (toFactSpan f)) of
            [] -> ()
            xs -> error $ "insertFacts: new fact (" ++ show (toFactSpan f)
                    ++ ") for " ++ show ix ++ " overlaps existing facts: " ++ show (toFactSpan <$> xs)
        FactE ix f -> case fst (cropView (unTimelineE (kbFactsE kb DMap.! ix)) (toFactSpan f)) of
            [] -> ()
            xs -> error $ "insertFacts: new fact (" ++ show (toFactSpan f)
                    ++ ") for " ++ show ix ++ " overlaps existing facts: " ++ show (toFactSpan <$> xs)

    -- Store the new fact.
    writeFact factTop

    -- Derive knowledge.
    case factTop of
        FactB (ix :: BIx a) (factB :: FactB a) -> do
            -- 1 Directly insert fact.
            modifyKB $ \ kb -> kb
                { kbFactsB = DMap.update
                    (Just . TimelineB . T.insertFact factB . unTimelineB)
                    ix
                    (kbFactsB kb)
                }

            -- Extrapolate forward what the curr/next values are in order to
            -- fire any active rules.

            -- The (current) value known just before the current fact's
            -- time span.
            -- For initial value facts, curr/next is just the initial value at X_NegInf.
            currAMay :: Maybe a <- asksKB $
                lookupBIx ix (fromMaybe X_NegInf $ factSpanJustBeforeMinT (toFactSpan factB))

            -- The (next) value known for the current fact's time span.
            -- For initial value facts, curr/next is just the initial value at X_NegInf.
            nextAMay :: Maybe a <- asksKB $
                lookupBIx ix (fromMaybe X_NegInf $ factSpanMinT (toFactSpan factB))

            kbFactsB' <- asksKB kbFactsB
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

            -- Extract dependent rules.
            ActiveRulesE activeRulesMT <- asksKB $ \kb -> kbActiveRulesE kb DMap.! ix
            let (extractedActiveRules, activeRulesMT') = mtCropView ar_factSpan activeRulesMT (toFactSpan factE)
            modifyKB $ \kb -> kb { kbActiveRulesE = DMap.update (const $ Just $ ActiveRulesE activeRulesMT') ix (kbActiveRulesE kb) }

            -- Continue dependent rules
            mapM_ (continueRule (factEToOcc factE)) (unMultiTimeline extractedActiveRules)
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



--
-- For internal use
--


-- | insert a value fact into the knowlege base. This will handle poking any
-- active rules.
insertNextValueFact
    :: FieldIx game
    => BIx a
    -> a
    -> FactSpan
    -> KnowledgeBaseM game ()
insertNextValueFact
    = insertValueFact
        kbActiveRulesBNext
        (\kb activeRules -> kb { kbActiveRulesBNext = activeRules })

insertValueFact
    :: FieldIx game
    => (KnowledgeBase game -> DMap BIx (ActiveRulesB game))
    -- ^ Get current or next active rules.
    -> (KnowledgeBase game -> DMap BIx (ActiveRulesB game) -> KnowledgeBase game)
    -- ^ Set current or next active rules.
    -> BIx a
    -> a
    -> FactSpan
    -> KnowledgeBaseM game ()
insertValueFact getActiveRules setActiveRules bix a valueFactSpan = do
    -- Find/remove all active rules who's time (span) intersects the value fact.
    ActiveRulesB activeRulesMT <- asksKB $ \kb -> (getActiveRules kb) DMap.! bix
    let (extractedActiveRules, activeRulesMT') = mtCropView ar_factSpan activeRulesMT valueFactSpan
    modifyKB $ \kb -> setActiveRules kb (DMap.update (const $ Just $ ActiveRulesB activeRulesMT') bix (getActiveRules kb))
    mapM_ (continueRule a) (unMultiTimeline extractedActiveRules)

continueRule :: FieldIx game => a -> ActiveRule game a -> KnowledgeBaseM game ()
continueRule a activeRule
    -- Step all the extracted active rules and reinsert them either as new
    -- active rules, or as facts (if the rule terminates).
    = case activeRule of
        ActiveRuleB factSpan finalFieldBIx continuationB ->
            -- TODO use changeDetected
            case continuationB a of
                Result r -> insertFact (FactB finalFieldBIx (case factSpan of
                    FS_Init -> Init r
                    FS_Point t -> ChangePoint t (MaybeChange (Just r))   -- TODO allow Rule to return "NoChange" for behaviours
                    FS_Span tspan -> ChangeSpan tspan NoChange
                    ))
                DependencyE eix cont -> insertActiveRuleE eix
                    (ActiveRuleB factSpan finalFieldBIx cont)
                DependencyB con bix cont -> insertActiveRuleB con bix
                    (ActiveRuleB factSpan finalFieldBIx cont)
        ActiveRuleE factSpan finalFieldEIx continuationE ->
            case continuationE a of
                Result r -> insertFact (FactE finalFieldEIx (case factSpan of
                    FS_Init -> error "Trying to set Init value of an Event but events don't have initial values. Did you accidentally insert a Rule for an event that spans all of time including the initial value?"
                    FS_Point t -> ChangePoint t r
                    FS_Span tspan -> ChangeSpan tspan NoChange
                    ))
                DependencyE eix cont -> insertActiveRuleE eix
                    (ActiveRuleE factSpan finalFieldEIx cont)
                DependencyB con bix cont -> insertActiveRuleB con bix
                    (ActiveRuleE factSpan finalFieldEIx cont)

-- | Insert the rule for an event (for all time). Note this does NOT insert an
-- active rule for FS_Init as events don't have init values.
insertRuleE :: FieldIx game
    => EIx a
    -> Rule game (Maybe a)
    -> KnowledgeBaseM game ()
insertRuleE eix rule = case rule of
    DependencyE depEix cont -> insertActiveRuleE depEix
        $ ActiveRuleE (FS_Span allT) eix cont
    DependencyB con depBix cont -> insertActiveRuleB con depBix
        $ ActiveRuleE (FS_Span allT) eix cont
    -- TODO WTF does this mean? An event that is always occurring? Do we allow this?
    Result _ -> error $ "Event definition must have at least 1 dependency: " ++ show eix

-- | Insert the rule for a behavior (for all time).
insertRuleB :: FieldIx game
    => BIx a
    -> Rule game a
    -> KnowledgeBaseM game ()
insertRuleB bix rule = case rule of
    DependencyE depEix cont -> insertActiveRuleE depEix
        $ ActiveRuleB (FS_Span allT) bix cont
    DependencyB con depBix cont -> insertActiveRuleB con depBix
        $ ActiveRuleB (FS_Span allT) bix cont
    Result r -> do
        insertFact (FactB bix (Init r))
        insertFact (FactB bix (ChangeSpan allT NoChange))

insertActiveRuleE :: forall game b . FieldIx game
    => EIx b                        -- ^ Active rule's current dependency
    -> ActiveRule game (Maybe b)    -- ^ Active rule
    -> KnowledgeBaseM game ()
insertActiveRuleE eix activeRule
    = insertActiveRule'
        (\kb -> unTimelineE $ kbFactsE kb DMap.! eix)
        (\ar kb -> kb
                { kbActiveRulesE = DMap.update
                    (\(ActiveRulesE mt) -> Just $ ActiveRulesE $ mtFromList [ar] `mtUnion` mt)
                    eix
                    (kbActiveRulesE kb)
                }
        )
        (\f _kb -> Just (factEToOcc f))
        eix
        activeRule

insertActiveRuleB :: forall game b . FieldIx game
    => CurrOrNext
    -> BIx b                -- ^ Active rule's current dependency
    -> ActiveRule game b    -- ^ Active rule
    -> KnowledgeBaseM game ()
insertActiveRuleB con bix activeRule
    = insertActiveRule'
        (\kb -> unTimelineB $ kbFactsB kb DMap.! bix)
        (case con of
            Curr -> \ar kb -> kb
                { kbActiveRulesBCurr = DMap.update
                    (\(ActiveRulesB mt) -> Just $ ActiveRulesB $ mtFromList [ar] `mtUnion` mt)
                    bix
                    (kbActiveRulesBCurr kb)
                }
            Next -> \ar kb -> kb
                { kbActiveRulesBNext = DMap.update
                    (\(ActiveRulesB mt) -> Just $ ActiveRulesB $ mtFromList [ar] `mtUnion` mt)
                    bix
                    (kbActiveRulesBNext kb)
                }
        )
        (case con of
            Curr -> \f kb -> lookupBIx bix (fromMaybe X_NegInf $ factSpanMinT $ toFactSpan f) kb
            Next -> \f kb -> case f of
                -- The only time Next is different from current is if the
                -- fact is a change in the behavior value.
                ChangePoint _ (MaybeChange (Just b)) -> Just b
                _ -> lookupBIx bix (fromMaybe X_NegInf $ factSpanMinT $ toFactSpan f) kb
        )
        bix
        activeRule

insertActiveRule'
    :: forall game b ix timeline id pd sd cvOutsize . (FieldIx game, CropView (timeline id pd sd) FactSpan [Fact' id pd sd] cvOutsize)
    => (KnowledgeBase game -> timeline id pd sd)
    -- ^ Get active rule's dependency's timeline
    -> (ActiveRule game b -> KnowledgeBase game -> KnowledgeBase game)
    -- ^ Directly insert an active rule (assuming the dependency is `ix`).
    -> (Fact' id pd sd -> KnowledgeBase game -> Maybe b)
    -- ^ From a fact about the dependency, and the current knowledge base,
    -- get the value of the dependency that should be used to continue the
    -- active rule. WARNING If this returns Nothing, the active rule will be
    -- inserted directly; you must ensure that the rule will eventually be
    -- fired via some other means.
    -> ix
    -- ^ Active rule's dependency's index.
    -> ActiveRule game b
    -- ^ The active rule.
    -> KnowledgeBaseM game ()
insertActiveRule' getTimeline directInsert depFactToValue ix activeRule = do
    timeline <- asksKB $ getTimeline
    let arFactSpan = ar_factSpan activeRule
        extractedFacts = crop timeline arFactSpan

    case extractedFacts of
        -- Base cases: no facts, just directly insert the active rule.
        [] -> modifyKB (directInsert activeRule)
        -- Base cases: fully overlapping fact, continue the rule.
        [f] | arFactSpan == toFactSpan f -> do
            depValueMay <- asksKB (depFactToValue f)
            case depValueMay of
                Nothing -> modifyKB (directInsert activeRule)
                Just depValue -> continueRule depValue activeRule

        -- Recursive case: split the active rule and insert the parts.
        _ -> do
            let notCoveredRules :: [FactSpan]
                notCoveredRules = arFactSpan `difference` (toFactSpan <$> extractedFacts)

                notCoveredActiveRules :: [ActiveRule game b]
                notCoveredActiveRules = case activeRule of
                    ActiveRuleB _ finalBix cont
                        -> [ ActiveRuleB s finalBix cont | s <- notCoveredRules ]
                    ActiveRuleE _ finalEix cont
                        -> [ ActiveRuleE s finalEix cont | s <- notCoveredRules ]

                -- THEN continue and insert the covered active rules
                coveredActiveRules :: [ActiveRule game b]
                coveredActiveRules = case activeRule of
                    ActiveRuleB _ finalBix cont
                        -> [ ActiveRuleB (toFactSpan fact) finalBix cont | fact <- extractedFacts ]
                    ActiveRuleE _ finalEix cont
                        -> [ ActiveRuleE (toFactSpan fact) finalEix cont | fact <- extractedFacts ]

            mapM_ (insertActiveRule' getTimeline directInsert depFactToValue ix) (notCoveredActiveRules ++ coveredActiveRules)

knTimelineB :: BIx a -> KnowledgeBase game -> TimelineB a
knTimelineB bix kb = kbFactsB kb DMap.! bix

knTimelineE :: EIx a -> KnowledgeBase game -> TimelineE a
knTimelineE eix kb = kbFactsE kb DMap.! eix

instance FieldIx game => Pretty (KnowledgeBase game) where
    pretty kb = vsep
        [ "KnowledgeBase:"
        , indent 2 $ vsep $
            traverseFields (fieldIxs @game)
                (\ix _ -> vsep
                    [ pretty ix <> ":"
                    , indent 2 $ vsep
                        [ pretty (knTimelineE ix kb)
                        , "ActiveRules: " <+> pretty (kbActiveRulesE kb DMap.! ix)
                        ]
                    ]
                )
                (\ix _ -> vsep
                    [ pretty ix <> ":"
                    , indent 2 $ vsep
                        [ pretty (knTimelineE ix kb)
                        , "ActiveRules: " <+> pretty (kbActiveRulesE kb DMap.! ix)
                        ]
                    ]
                )
                (\ix _ -> vsep
                    [ pretty ix <> ":"
                    , indent 2 $ vsep
                        [ pretty (knTimelineB ix kb)
                        , "ActiveRules Curr: " <+> pretty (kbActiveRulesBCurr kb DMap.! ix)
                        , "ActiveRules Next: " <+> pretty (kbActiveRulesBNext kb DMap.! ix)
                        ]
                    ]
                )
        ]

instance FieldIx game => Show (KnowledgeBase game) where
    showsPrec _ = renderShowS . layoutPretty defaultLayoutOptions . pretty

instance Pretty (BIx a) where pretty = viaShow
instance Pretty (EIx a) where pretty = viaShow

instance Pretty (ActiveRulesE game a) where pretty = viaShow . fmap ar_factSpan . unMultiTimeline . unActiveRulesE
instance Pretty (ActiveRulesB game a) where pretty = viaShow . fmap ar_factSpan . unMultiTimeline . unActiveRulesB

instance Pretty (Fact game) where
    pretty (FactB ix f) = "FactB (" <> pretty ix <> ") " <> pretty (toFactSpan f)
    pretty (FactE ix f) = "FactE (" <> pretty ix <> ") " <> pretty (toFactSpan f)








--
-- IX Stuff
--



data FieldType
    = SourceEvent
    | Event
    | Behavior

data GameData
    = Raw
    | Index
    | Definition

newtype Field game fieldType gameData a = Field { unF :: F game fieldType gameData a }

type family F (game :: GameData -> Type) (fieldType :: FieldType) (gameData :: GameData) a :: Type where

    F _ 'SourceEvent 'Raw a = Maybe a
    F _ 'Event       'Raw a = Maybe a
    F _ 'Behavior    'Raw a = a

    F _ 'SourceEvent 'Index a = EIx a
    F _ 'Event       'Index a = EIx a
    F _ 'Behavior    'Index a = BIx a

    F _    'SourceEvent 'Definition a = SourceEventDef a
    F game 'Event       'Definition a = EventDef game a
    F game 'Behavior    'Definition a = BehaviorDef game a

type B  game f a = Field game 'Behavior    f a
type E  game f a = Field game 'Event       f a
type SE game f a = Field game 'SourceEvent f a

newtype EIx a = EIx Int deriving (Eq, Ord, Show)
newtype BIx a = BIx Int deriving (Eq, Ord, Show)
-- data Ix a = Ix_B (BIx a) | Ix_E (EIx a)

type KeyB  game (a :: Type) = forall (gameData :: GameData) . game gameData -> Field game 'Behavior    gameData a
type KeyE  game (a :: Type) = forall (gameData :: GameData) . game gameData -> Field game 'Event       gameData a
type KeySE game (a :: Type) = forall (gameData :: GameData) . game gameData -> Field game 'SourceEvent gameData a
-- data Key game (a :: Type)
--     = KeyB (KeyB game a)
--     | KeyE (KeyE game a)

class FieldIx (game :: GameData -> *) where
    fieldIxs :: game 'Index
    default fieldIxs :: (Generic (game 'Index), GFieldIxs (Rep (game 'Index))) => game 'Index
    fieldIxs = to $ gFieldIxs 0

    traverseFields
        :: game gameData
        -> (forall x . EIx x -> Field game 'SourceEvent gameData x -> a)
        -> (forall x . EIx x -> Field game 'Event       gameData x -> a)
        -> (forall x . BIx x -> Field game 'Behavior    gameData x -> a)
        -> [a]
    default traverseFields :: (Generic (game gameData), GTraverseGame (Rep (game gameData)) game gameData)
        => game gameData
        -> (forall x . EIx x -> Field game 'SourceEvent gameData x -> a)
        -> (forall x . EIx x -> Field game 'Event       gameData x -> a)
        -> (forall x . BIx x -> Field game 'Behavior    gameData x -> a)
        -> [a]
    traverseFields g = gTraverseFields 0 (from g)

eIx :: (F game eventType 'Index a ~ EIx a, FieldIx game)
    => (game 'Index -> Field game eventType 'Index a)
    -> EIx a
eIx k = unF (k fieldIxs)

bIx :: FieldIx game => KeyB game a -> BIx a
bIx k = unF (k fieldIxs)

--
-- Generic FieldIx
--

class GFieldIxs a where
    gFieldIxs :: Int -> a
instance GFieldIxs (NP I xs) => GFieldIxs (SOP I '[xs]) where
    gFieldIxs ix = SOP (Z (gFieldIxs ix))
instance GFieldIxs (NP I '[]) where
    gFieldIxs _ = Nil
instance (F game 'SourceEvent 'Index a ~ EIx a, GFieldIxs (NP I xs)) => GFieldIxs (NP I (Field game 'SourceEvent 'Index a ': xs)) where
    gFieldIxs ix = I (Field $EIx ix) :* gFieldIxs (ix + 1)
instance (F game 'Event 'Index a ~ EIx a, GFieldIxs (NP I xs)) => GFieldIxs (NP I (Field game 'Event 'Index a ': xs)) where
    gFieldIxs ix = I (Field $EIx ix) :* gFieldIxs (ix + 1)
instance (F game 'Behavior 'Index a ~ BIx a, GFieldIxs (NP I xs)) => GFieldIxs (NP I (Field game 'Behavior 'Index a ': xs)) where
    gFieldIxs ix = I (Field $BIx ix) :* gFieldIxs (ix + 1)

class GTraverseGame rep game gameData where
    gTraverseFields
        :: Int -- ^ current index
        -> rep
        -> (forall x . EIx x -> Field game 'SourceEvent gameData x -> a)
        -> (forall x . EIx x -> Field game 'Event       gameData x -> a)
        -> (forall x . BIx x -> Field game 'Behavior    gameData x -> a)
        -> [a]
instance (GTraverseGame (NP I xs) game gameData) => GTraverseGame (SOP I '[xs]) game gameData where
    gTraverseFields ix game fse fe fb = gTraverseFields ix (unZ $ unSOP $ game) fse fe fb
instance GTraverseGame (NP I '[]) game gameData where
    gTraverseFields _ _ _ _ _ = []
instance GTraverseGame (NP I xs) game gameData => GTraverseGame (NP I ((Field game 'SourceEvent gameData x) ': xs)) game gameData where
    gTraverseFields ix game fse fe fb = (fse (EIx ix) $ unI $ hd game) : gTraverseFields (ix + 1) (tl game) fse fe fb
instance GTraverseGame (NP I xs) game gameData => GTraverseGame (NP I ((Field game 'Event gameData x) ': xs)) game gameData where
    gTraverseFields ix game fse fe fb = (fe (EIx ix) $ unI $ hd game) : gTraverseFields (ix + 1) (tl game) fse fe fb
instance GTraverseGame (NP I xs) game gameData => GTraverseGame (NP I ((Field game 'Behavior gameData x) ': xs)) game gameData where
    gTraverseFields ix game fse fe fb = (fb (BIx ix)$ unI $ hd game) : gTraverseFields (ix + 1) (tl game) fse fe fb
