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
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module KnowledgeBase where

import Control.Monad
import qualified Data.Map as Map
import Data.Map (Map, (!?))
import Data.Maybe (fromMaybe)

import Time
import TimeSpan

-- Describes all the data E/Bs of the game (and inputs)
data Game sourceEvent event behavior = Game
    { player1InputA :: sourceEvent ()
    , player1InputB :: sourceEvent ()
    , player2InputA :: sourceEvent ()
    , player2InputB :: sourceEvent ()
    , player1Pos :: behavior Pos
    , player2Pos :: behavior Pos
    , arePlayersOverlapping :: behavior Bool
    }
type Pos = (Int, Int)

data SourceEventDef a   = SourceEvent
data BehaviorDef game a = BehaviorDef [FactTCB a] (Rule game a)
data EventDef    game a = EventDef    [FactTCE a] (Rule game a)

gameLogic :: Game SourceEventDef (EventDef Game) (BehaviorDef Game)
gameLogic = Game
    { player1InputA = SourceEvent
    , player1InputB = SourceEvent
    , player2InputA = SourceEvent
    , player2InputB = SourceEvent
    , player1Pos
        = foldB (0,0) $ do
            occA <- getE player1InputA
            occB <- getE player1InputB
            case (occA, occB) of
                (Just (), _) -> return (1,0)
                (_, Just ()) -> return (0,1)
                (Nothing, Nothing) -> getB player1Pos
    , player2Pos
        = foldB (0,0) $ do
            occA <- getE player2InputA
            occB <- getE player2InputB
            case (occA, occB) of
                (Just (), _) -> return (1,0)
                (_, Just ()) -> return (0,1)
                (Nothing, Nothing) -> getB player2Pos
    , arePlayersOverlapping
        = behavior $ do
            p1 <- getB player1Pos
            p2 <- getB player2Pos
            return (p1 == p2)
    }

-- TODO use generics to do this

-- TODO make Rules return maybe a change

type Any = String -- TODO to avoid type stuff I'm just using Any everywhere

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

type KeyB game a = forall e b . game e e b -> b a
type KeyE game a = forall e b . game e e b -> e a
data Key game a
    = KeyB (KeyB game a)
    | KeyE (KeyE game a)

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

data Fact game a
    = FactB (KeyB game a) (FactTCB a)
    | FactE (KeyE game a) (FactTCE a)

data FactTCB a
    = Init a
    | Change Time (Maybe a)
    | NoChange SpanExc

data Occ a = Occ a | NoOcc

data FactTCE a
    = FactOcc Time (Occ a)
    | FactNoOcc SpanExc

--
-- Combinators
--

-- | For a single field, some initial facts (if any) and the corresponding rule.
foldB :: a -> Rule game a -> BehaviorDef game a
foldB aInit rule = BehaviorDef [(Init aInit)] rule

behavior :: Rule game a -> BehaviorDef game a
behavior rule = BehaviorDef [] rule

{- IMPLEMENTATION NOTES

kbFacts may gain NoChange knowlage before for a span of time before we gain
knowledge of the actual value for that span. If we maintain the NoChange span
invariant, then we can simply run all active rules only when we gain knowlage of
the actual value which can happen only when we insert a `Change t (Just a)`
value (pussibly just before a NoChange span) At that point we must progress
active rules covering that span.
-}

-- | All knowledge about all fields and meta-knowledge.
data KnowledgeBase game = KnowledgeBase
    { kbFacts :: game
                    KBFactsE
                    KBFactsE
                    KBFactsB
    -- ^ All rules in general key is the rule's first Dependency, value is the
    -- list of (Field the rule is for, rule for the field). Note that if a rule
    -- has no dependencies, then that field should just have fact(s) covering
    -- all time.
    --
    -- **invariant** that there are no neighboring NoChange facts (neighboring
    -- means separated by no time, i.e. no unknown space between facts) in the
    -- form [NoChange _, Change _ Nothing, NoChange _]`. This must always be
    -- simplified to a single [NoChange _] with a full span.
    , kbValues
        :: game
            KBValuesE
            KBValuesE
            KBValuesB
    -- ^ The actual values for each time (no NoChange nonsense)
    , kbActiveRules
        :: game
            (KbActiveRulesE game)
            (KbActiveRulesE game)
            (KbActiveRulesB game)
    -- ^ For each Field, f, a map from rule span start to rule spans and rule
    -- continuations. f is the rule's current dependency
    --
    -- All rules are initialized to their first dependency spanning all of
    -- time. Hence a rule will be fully discharged exactly once for all time,
    -- though will usually be split (potentially many times) into smaller spans.
    -- as facts are inserted.
    --
    -- TODO! PERFORMANCE!
    --
    -- I think this wil have a high impact, as we'll probably be recalculating
    -- behaviours 1 once per unsynchronized source event.
    --
    -- Since we are aware of value's not changing, there are a lot of
    -- optimizations that can be made here. In particular, a rule may be split
    -- many times, but if nothing has changed, we dont want to recalculate the
    -- value. We should be able to merge neighboring spans into a single
    -- NoChange span. We'd need to know if partially applied rules are equal,
    -- and I think we can do this by tagging them with the index of thier
    -- original (non-partially applied rule) and also the number of partial
    -- applications. In general, that doesn't imply equality, but when the
    -- dependencies so far are all NoChange, and the partially applied rules are
    -- in neighboring time spans, then this does imply equality.

    -- All Active rules indexed by their current dependency.
    -- Value is a map from rule's span min time to (rule's span andfield and span lo time
    }

-- Facts contain either Change/NoChange facts, or solid values
newtype KBFactsE a = KBFactsE           (Map TimeX (Either (SpanIncExc, a, a) (FactTCE a)))
data    KBFactsB a = KBFactsB (Maybe a) (Map TimeX (Either (SpanIncExc, a, a) (FactTCB a)))

newtype KBValuesE a = KBValuesE           (Map TimeX (FactTCE a))
data    KBValuesB a = KBValuesB (Maybe a) (Map TimeX (SpanIncExc, a))

newtype KbActiveRulesE game a = KbActiveRulesE (Map TimeX [ActiveRule game a])
newtype KbActiveRulesB game a = KbActiveRulesB (Map TimeX [ActiveRule game a])
data    ActiveRule game a = forall b . ActiveRule
                                Bool   -- ^ Has any of the deps so far actually indicated a change?
                                (Either Time SpanExc) -- ^ result and dependencies span this time exactly.
                                (Key game b)  -- ^ result is for this field
                                (a -> Rule game b) -- ^ Continuation

{-

-- type    KBRulesE game a = Ap3 game [(Key, Rule Any)]
-- type Ap2 game e b = game e e b
-- type Ap3 game a   = game a a a

lookupKB :: Field -> TimeX -> KnowledgeBase -> Maybe Any
lookupKB field tx knowledgeBase@(KnowledgeBase kb _ _) = do
    (negInf, _) <- Map.lookup field kb
    fact <- lookupKBFact field tx knowledgeBase
    case fact of
        FactTCB (Init a) -> Just a
        FactTCB (Change _ a) -> Just a
        FactTCB (NoChange tspan) -> case spanExcJustBefore tspan of
            Nothing -> negInf
            Just t -> lookupKB field (toTime t) knowledgeBase
        FactTCE (FactOcc _ a) -> Just a
        FactTCE (FactNoOcc _) -> Nothing


lookupKBFact :: Field -> TimeX -> KnowledgeBase -> Maybe (FactTimeValue Any)
lookupKBFact field tx (KnowledgeBase kb _ _) = do
    (negInf, fieldFacts) <- Map.lookup field kb
    if tx == X_NegInf
        then FactTCB . Init <$> negInf
        else do
            (_, fact)       <- Map.lookupLE tx fieldFacts
            guard $ case fact of
                FactTCB (Init _) -> tx == X_NegInf
                FactTCB (Change t _) -> tx == X_Exactly t
                FactTCB (NoChange tspan) -> tspan `contains` tx
                FactTCE (FactOcc t _) -> tx == X_Exactly t
                FactTCE (FactNoOcc tspan) -> tspan `contains` tx
            return fact

factLoTime :: FactTimeValue a -> Maybe TimeX
factLoTime f = case f of
    FactTCB (Init _) -> Nothing
    FactTCB (Change t _) -> Just (X_Exactly t)
    FactTCB (NoChange tspan) -> Just (spanExcMinT tspan)
    FactTCE (FactOcc t _) -> Just (X_Exactly t)
    FactTCE (FactNoOcc tspan) -> Just (spanExcMinT tspan)

insertFacts
    :: KnowledgeBase
    -- ^ Current KnowledgeBase.
    -> [Fact Any]
    -- ^ New Facts
    -> ( KnowledgeBase
       -- ^ New KnowledgeBase.
       , [FactTimeValue Any]
       -- ^ New derived facts (excluding the passed new facts)
       )
insertFacts knowledgeBaseTop
    = foldl
        (\(kb, fs) f -> let (kb', fs') = insertFact f kb in (kb', fs' ++ fs))
        (knowledgeBaseTop, [])

insertFact :: Fact Any -> KnowledgeBase -> (KnowledgeBase, [FactTimeValue Any])
insertFact fact kb
    | not (null overlaps) = error $ "insertFacts: new fact ("
                                ++ show fact
                                ++ ") overlaps existing facts: "
                                ++ show overlaps
    | otherwise = (kb', newFacts)
    where
    -- 1. Directly insert the fact into the knowledge base.
    kbFacts' = kbFactsInsertDirect fact (kbFacts kb)

    -- 2. Insert new active rules that depend on the newly inserted fact.
    --    NOTE that we're only concerned with changes in value.

    -- 3. Poke (i.e. reinsert) all active rules that depend on the newly
    --    inserted fact.



    kbFactsInsertDirect
        :: Fact Any
        -> Map Field (Maybe Any, Map TimeX (FactTimeValue Any))
        -> Map Field (Maybe Any, Map TimeX (FactTimeValue Any))
    kbFactsInsertDirect (Fact field fact)
        = Map.alter
            (\filedFactsMay -> do
                let (initMay, fieldValsMap) = fromMaybe (Nothing, Map.empty) filedFactsMay
                Just $ case fact of
                    FactTCB (Init a) -> (Just a, fieldValsMap)
                    _ -> ( initMay
                         , Map.insert
                            (fromMaybe (error "kbFactsInsertDirect: Impossible! fact has no low time but isn't behavior init value")
                                (factLoTime fact)
                            )
                            fact
                            fieldValsMap
                         )
            )
            field

    kb' :: KnowledgeBase
    kb' = KnowledgeBase kbFacts' _ _

    newFacts :: [FactTimeValue Any]
    newFacts = _

    overlaps :: [(Field, FactTimeValue Any)]
    overlaps = _

    -- Insert a rule:ArePlayersOverlapping
    -- 1. Evaluate the rule as much as possible
    -- 2. Either
    --      * Insert the active rule, or if terminated with a fact...
    --      * Insert the fact with insertFact.
    insertActiveRule
        :: (Field, TimeX)    -- ^ rule's next dependency
        -> (Any -> Rule Any) -- ^ rule's continuation after getting dependency
        -> KnowledgeBase -> (KnowledgeBase, [FactTimeValue Any])
    insertActiveRule = _
    -}