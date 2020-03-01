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


gameLogic :: [Definition Any]
gameLogic =
    [ ( FieldB Player1Pos
      , foldB "(0,0)" $ do
            occA <- getE Player1InputA
            occB <- getE Player1InputB
            case (occA, occB) of
                ("Just ()", _) -> return "(1,0)"
                (_, "Just ()") -> return "(0,1)"
                ("Nothing", "Nothing") -> getB Prev Player1Pos
                _ -> undefined
      )

    , ( FieldB Player2Pos
      , foldB "(0,0)" $ do
            occA <- getE Player2InputA
            occB <- getE Player2InputB
            case (occA, occB) of
                ("Just ()", _) -> return "(1,0)"
                (_, "Just ()") -> return "(0,1)"
                ("Nothing", "Nothing") -> getB Prev Player2Pos
                _ -> undefined
      )

    , ( FieldB ArePlayersOverlapping
      , behavior $ do
            p1 <- getB Curr Player1Pos
            p2 <- getB Curr Player2Pos
            return (show $ p1 == p2)
      )
    ]

-- TODO make Rules return maybe a change

type Any = String -- TODO to avoid type stuff I'm just using Any everywhere

-- Describes all the data E/Bs of the game (and inputs)
data Field
    = FieldB FieldB
    | FieldE FieldE
    deriving (Eq, Ord, Show)

data FieldE
    = Player1InputA
    | Player1InputB
    | Player2InputA
    | Player2InputB
    deriving (Eq, Ord, Show)

data FieldB
    = Player1Pos
    | Player2Pos
    | ArePlayersOverlapping
    deriving (Eq, Ord, Show)

data PrevOrCurr = Prev | Curr
data Rule a
    = Dependency PrevOrCurr Field -- TODO assumes Filed has type `a`
    -- ^ Dependency on some other field in previous time or current time (PrevOrCurr).
    | RuleResult a
    | forall b . BindRule (Rule b) (b -> Rule a)

getB :: PrevOrCurr -> FieldB -> Rule Any
getB poc field = Dependency poc (FieldB field)

getE :: FieldE -> Rule Any  -- Actually returns:   Rule (Maybe a)
getE field = Dependency Curr (FieldE field)

instance Functor Rule where
    fmap f r = BindRule r (pure . f)
instance Applicative Rule where
    pure = RuleResult
    ra2b <*> ra = do
        a2b <- ra2b
        a   <- ra
        return (a2b a)
instance Monad Rule where
    (>>=) = BindRule

data FieldFact a = FieldFact
    { ffField :: Field
    , ffFactTimeValue :: FactTimeValue a
    }
    deriving (Show)

data FactTimeValue a
    = FactTimeValueB (FactTimeValueB a)
    | FactTimeValueE (FactTimeValueE a)
    deriving (Show)

data FactTimeValueB a
    = Init a
    | Change Time a
    | NoChange SpanExc
    deriving (Show)

data FactTimeValueE a
    = FactOcc Time a
    | FactNoOcc SpanExc
    deriving (Show)


--
-- Combinators
--

-- | For a single field, some initial facts (if any) and the corresponding rule.
type Definition a = (Field, ([FactTimeValue a], Rule a))

foldB :: a -> Rule a -> ([FactTimeValue a], Rule a)
foldB aInit rule = ([FactTimeValueB (Init aInit)], rule)

behavior :: Rule a -> ([FactTimeValue a], Rule a)
behavior rule = ([], rule)



-- | All knowledge about all fields and meta-knowledge.
data KnowledgeBase = KnowledgeBase
    { kbFacts :: Map Field
        ( Maybe Any
        , Map TimeX (FactTimeValue Any))
    -- ^ All the known facts (fst is initial value (only applicable for behaviors))
    , kbRules :: Map Field [(Field, Rule Any)]
    -- ^ All rules in general key is the rule's first Dependency, value is the list of
    -- (Field the rule is for, rule for the field).
    -- Note that if a rule has no dependencies, then that field should just have fact(s)
    -- covering all time.
    , kbActiveRules :: Map (Field, TimeX) [(Any -> Rule Any)]
    -- ^ All Active rules indexed by their current dependency field and span lo time
    }

lookupKB :: Field -> TimeX -> KnowledgeBase -> Maybe Any
lookupKB field tx knowledgeBase@(KnowledgeBase kb _ _) = do
    (negInf, _) <- Map.lookup field kb
    fact <- lookupKBFact field tx knowledgeBase
    case fact of
        FactTimeValueB (Init a) -> Just a
        FactTimeValueB (Change _ a) -> Just a
        FactTimeValueB (NoChange tspan) -> case spanExcJustBefore tspan of
            Nothing -> negInf
            Just t -> lookupKB field (toTime t) knowledgeBase
        FactTimeValueE (FactOcc _ a) -> Just a
        FactTimeValueE (FactNoOcc _) -> Nothing


lookupKBFact :: Field -> TimeX -> KnowledgeBase -> Maybe (FactTimeValue Any)
lookupKBFact field tx (KnowledgeBase kb _ _) = do
    (negInf, fieldFacts) <- Map.lookup field kb
    if tx == X_NegInf
        then FactTimeValueB . Init <$> negInf
        else do
            (_, fact)       <- Map.lookupLE tx fieldFacts
            guard $ case fact of
                FactTimeValueB (Init _) -> tx == X_NegInf
                FactTimeValueB (Change t _) -> tx == X_Exactly t
                FactTimeValueB (NoChange tspan) -> tspan `contains` tx
                FactTimeValueE (FactOcc t _) -> tx == X_Exactly t
                FactTimeValueE (FactNoOcc tspan) -> tspan `contains` tx
            return fact

factLoTime :: FactTimeValue a -> Maybe TimeX
factLoTime f = case f of
    FactTimeValueB (Init _) -> Nothing
    FactTimeValueB (Change t _) -> Just (X_Exactly t)
    FactTimeValueB (NoChange tspan) -> Just (spanExcMinT tspan)
    FactTimeValueE (FactOcc t _) -> Just (X_Exactly t)
    FactTimeValueE (FactNoOcc tspan) -> Just (spanExcMinT tspan)

insertFacts
    :: KnowledgeBase
    -- ^ Current KnowledgeBase.
    -> [FieldFact Any]
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

insertFact :: FieldFact Any -> KnowledgeBase -> (KnowledgeBase, [FactTimeValue Any])
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
        :: FieldFact Any
        -> Map Field (Maybe Any, Map TimeX (FactTimeValue Any))
        -> Map Field (Maybe Any, Map TimeX (FactTimeValue Any))
    kbFactsInsertDirect (FieldFact field fact)
        = Map.alter
            (\filedFactsMay -> do
                let (initMay, fieldValsMap) = fromMaybe (Nothing, Map.empty) filedFactsMay
                Just $ case fact of
                    FactTimeValueB (Init a) -> (Just a, fieldValsMap)
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