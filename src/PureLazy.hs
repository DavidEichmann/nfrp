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

module PureLazy where

import Control.Concurrent
import Control.Monad
import qualified Data.Map as Map
import Data.Map (Map)

import FRP
import Time
import TimeSpan

-- TODO make Rules return maybe a change

type Any = String -- TODO to avoid type stuff I'm just using Any everywhere

-- Describes all the data E/Bs of the game (and inputs)
data Field
    = FieldB FieldB
    | FieldE FieldE
    deriving (Eq, Ord)

data FieldE
    = Player1InputA
    | Player1InputB
    | Player2InputA
    | Player2InputB
    deriving (Eq, Ord)

data FieldB
    = Player1Pos
    | Player2Pos
    | ArePlayersOverlapping
    deriving (Eq, Ord)

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

data Fact a
    = FactB (FactB a)
    | FactE (FactE a)

data FactB a
    = Init a
    | Change Time a
    | NoChange SpanExc

data FactE a
    = FactOcc Time a
    | FactNoOcc SpanExc

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


--
-- Combinators
--

-- | For a single field, some initial facts (if any) and the corresponding rule.
type Definition a = (Field, ([Fact a], Rule a))

foldB :: a -> Rule a -> ([Fact a], Rule a)
foldB aInit rule = ([FactB (Init aInit)], rule)

behavior :: Rule a -> ([Fact a], Rule a)
behavior rule = ([], rule)



-- | All knowledge about all fields and meta-knowledge.
data KnowledgeBase = KnowledgeBase
    (Map Field
        ( Maybe Any  -- ^ behavior initial value if a behavior and if known
        , Map TimeX (Fact Any))
    )
    -- ^ All the known facts
    (Map Field [(Field, Rule Any)])
    -- ^ All rules in general key is the rule's first Dependency, value is the list of
    -- (Field the rule is for, rule for the field).
    -- Note that if a rule has no dependencies, then that field should just have fact(s)
    -- covering all time.
    (Map (Field, TimeX) [(Any -> Rule Any)])
    -- ^ All Active rules indexed by their current dependency field/time

lookupKB :: Field -> TimeX -> KnowledgeBase -> Maybe Any
lookupKB field tx knowledgeBase@(KnowledgeBase kb) = do
    (negInf, _) <- Map.lookup field kb
    fact <- lookupKBFact field tx knowledgeBase
    case fact of
        FactB (Init a) -> Just a
        FactB (Change _ a) -> Just a
        FactB (NoChange tspan) -> case spanExcJustBefore tspan of
            Nothing -> negInf
            Just t -> lookupKB field (toTime t) knowledgeBase
        FactE (FactOcc _ a) -> Just a
        FactE (FactNoOcc _) -> Nothing


lookupKBFact :: Field -> TimeX -> KnowledgeBase -> Maybe (Fact Any)
lookupKBFact field tx (KnowledgeBase kb) = do
    (negInf, fieldFacts) <- Map.lookup field kb
    if tx == X_NegInf
        then FactB . Init <$> negInf
        else do
            (_, fact)       <- Map.lookupLE tx fieldFacts
            guard $ case fact of
                FactB (Init _) -> tx == X_NegInf
                FactB (Change t _) -> tx == X_Exactly t
                FactB (NoChange tspan) -> tspan `contains` tx
                FactE (FactOcc t _) -> tx == X_Exactly t
                FactE (FactNoOcc tspan) -> tspan `contains` tx
            return fact

stepKnowledgeBase
    :: KnowledgeBase
    -- ^ Current KnowledgeBase.
    -> [Fact Any]
    -- ^ New Facts
    -> ( KnowledgeBase
       -- ^ New KnowledgeBase.
       , [Fact Any]
       -- ^ New derived facts (excluding the passed new facts)
       )
stepKnowledgeBase = let
    --
    in _