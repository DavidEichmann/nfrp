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
import Data.Map (Map)

import FRP
import Time
import TimeSpan (SpanExc)

-- TODO!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! We must take special care
-- that Occ can't be directly created, else the programmer will likely create a
-- non instantaneous event.

-- | Overall we want a generic ish system such that we can specify state
-- transitions in a simple format. This is be expressed as a state type...

data Player = Player1 | Player2

data Game f = Game
    -- Source Input Events
    { player1InputA :: SE f ()
    , player1InputB :: SE f ()
    , player2InputA :: SE f ()
    , player2InputB :: SE f ()
    -- Derived State
    , player1Pos :: B f (Int, Int)
    , player2Pos :: B f (Int, Int)
    , arePlayersOverlapping :: B f Bool
    }

-- ... and a transition "function" expressed like so:

type UpdateFn game = game Symbolic -> game Definition

stepGame :: Game Symbolic -> Game Definition
stepGame gamePrev = define $ \ gameCurr ->  Game
    -- Source Inputs need no update
    { player1InputA = ()
    , player1InputB = ()
    , player2InputA = ()
    , player2InputB = ()
    -- State
    , player1Pos = foldB (0,0) $ do
        occA <- getE (player1InputA gameCurr)
        occB <- getE (player1InputB gameCurr)
        return $ case (occA, occB) of
            (Just (), _) -> Update (1,0)
            (_, Just ()) -> Update (0,1)
            (Nothing, Nothing) -> NoUpdate
    , player2Pos = foldB (0,0) $ do
        occA <- getE (player2InputA gameCurr)
        occB <- getE (player2InputB gameCurr)
        return $ case (occA, occB) of
            (Just (), _) -> Update (1,0)
            (_, Just ()) -> Update (0,1)
            (Nothing, Nothing) -> NoUpdate
    , arePlayersOverlapping = behavior $ do
        p1 <- getB $ player1Pos gameCurr
        p2 <- getB $ player2Pos gameCurr
        return (p1 == p2)
    }








-- | withCurrent is like fix in that it allows you to refer to the current state.
define :: (game Symbolic -> game Definition) -> game Definition
define = _

-- | Fold a behavior from and initial value and some updates
foldB :: a -> BMonad (Update a) -> BDefinition a
foldB = _

-- | Define a behavior
behavior :: BMonad a -> BDefinition a
behavior = _

-- | Wraps behaviors in the state type.
type family B  f a
-- | Wraps events in the state type.
type family E  f a
-- | Wraps source events in the state type.
type family SE f a

-- | Sample represents a snapshot of the game state at a given time. In stepGame,
-- gamePrev implicitly represents the snapshot of the game just before this
-- step (i.e. the previous state).
data Sample
type instance B  Sample     a = a
type instance E  Sample     a = Occ a
type instance SE Sample     a = Occ a

-- | Think of this as a symbolic version of Sample where the values are wrapped.
data Symbolic
type instance B  Symbolic   a = SymbolB a
type instance E  Symbolic   a = SymbolE a
type instance SE Symbolic   a = SymbolE a

-- | Defines how a type is stepped and also its initial values
data Definition
type instance B Definition a = BDefinition a
type instance E Definition a = EDefinition a
type instance SE Definition a = ()

-- | Used to build a behavior
data BMonad a
instance Functor BMonad where -- TODO
instance Applicative BMonad where -- TODO
instance Monad BMonad where -- TODO

getB :: SymbolB a -> BMonad a
getB = _

getE :: SymbolE a -> BMonad (Maybe a)
getE = _

-- | Definition of a single behavior
data BDefinition a

-- | Definition of a single event
data EDefinition a

-- | If a behavior should be updated or remain the same
data Update a = Update a | NoUpdate

-- | A symbolic value
data SymbolB a
data SymbolE a

--
-- Interfacing with the outside world
--

-- Now that we've defined our Game type and stepGame function we want some way
-- to run it and fire *partial* events. Partial events are event occurrences
-- over an explicit time span. The time span is important because we are
-- interested in knowing if we have complete knowledge or not.
--
-- Note that partial events may provide knowledge for only some source events
-- within the Game type i.e. knowledge of source events are independent! E.g. we
-- may know all events for player 1 at time t=0 to t=100, but only know player
-- 2's events from t=0 to t=10 and t=20 to t=70, due to network latency and
-- dropped/out-of-order packets.

-- So how do we represent partial knowledge? Since individual Behaviours and
-- events have independent knowledge time spans, we need a datatype per B/E
-- capturing a time span and changes in that time span:

data Fact a
    = NoChanges SpanExc
    -- ^ No updates (or event occurrence) for that time span
    | Change Time (Maybe a)
    -- ^ a possible update (or event occurrence) of the value at this.
type Knowledge a = [Fact a]

-- Great! All behaviours/events are ultimately defined in terms of source
-- events, so we need a way to stream chunks of knowledge - transactions - about
-- those source events into a function and get a corresponding stream of updates
-- for all B/Es (not just source events):

data SETransaction
type instance B  SETransaction a = ()
type instance E  SETransaction a = ()
type instance SE SETransaction a = Knowledge a

data TransactionResult
type instance B  TransactionResult a = Knowledge a  -- ^ NEW knowledge
type instance E  TransactionResult a = Knowledge a  -- ^ NEW knowledge
type instance SE TransactionResult a = Knowledge a  -- ^ NEW knowledge

newtype Actuated' game = Actuated' [game TransactionResult]

actuate'
    :: forall game
    .  (game Symbolic -> game Definition)
    -> [game SETransaction]
    -> Actuated' game
actuate' prevSybolicGameToDef allTransactions = Actuated' (go allTransactions)
    where
    go :: [game SETransaction] -> [game TransactionResult]
    go (t:ts) = let
        result = _
        in result : go ts

-- START Actuation stuff vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv

-- We probably will always be observing the "HEAD" state, so let's optimize
-- for that use case. So we represent a state between each transaction as
-- the Game with each E/B having the latest knowledge (or lack there of) of
-- values/events since just before the last gap in knowledge.

-- | Knowledge is always in reverse chronological order and ends just before
-- (chronologically) the oldest gap of knowledge
data ActState
type instance B  TransactionResult a = Knowledge a
type instance E  TransactionResult a = Knowledge a
type instance SE TransactionResult a = Knowledge a

-- STOP Actuation stuff ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


-- Now that we have a TimeLine, what do we do with it? Ultimately we'd like to
-- present the game to the user in some shape or form. Remember that knowledge
-- of each part of the game is independent, and perhaps (with some more advanced
-- future feature) some users may never know the full Game state at any give
-- time (past or present).
--
-- TODO how will prediction/reconciliation come into play here?
--
-- For now, let's just do the most obvious thing and present the most up to date
-- consistent Game state. This is effectively a Lock-Step implementation though
-- gaps in knowledge may be "skipped" if later states are known (implying that
-- those later states don't depend on that previous knowledge). Since we can
-- skip gaps in knowledge, we may skip event occurrences. Hence we can't
-- reliably present events in this model, so we don't report them at all.

data Sample_LatestConsistent
type instance B  Sample_LatestConsistent a = a
type instance E  Sample_LatestConsistent a = ()
type instance SE Sample_LatestConsistent a = ()

latestUpdates :: Actuated' game -> [game Sample_LatestConsistent]
latestUpdates = _

--
-- Networking
--

-- When it comes to networking, we are (currently) taking the approach of
-- sending all inputs. This makes things simple. Source Events correspond
-- exactly to the events we need to network. We also go right ahead and assume
-- that the a main game loop is running and observing inputs as time progresses
-- forward. Hence we can provide a single "fire events" function that fires events.
-- We also take care of clock synchronization.

data SESample
type instance B  SESample a = ()
type instance E  SESample a = ()
type instance SE SESample a = Maybe a  -- ^ Event if it is occurring

newtworkActuate
    :: node
    -- ^ Current node
    -> (node -> input -> game SETransaction)
    -- ^ Convert a node's inputs into a transaction.
    -> Map node (String, String)
    -- ^ (host, port) of nodes (Should be total including thisNode)
    -> UpdateFn game
    -> IO ( ThreadId
          , (Maybe input) -> IO ()
          -- ^ Fire input event for this node (Or nothing to indicate a lack of events).
          , [game TransactionResult]
          -- ^ Resulting stream of transactions.
          )
newtworkActuate = _

-- sourceEvents
--     :: forall node input
--     .  ( Eq node, Ord node, Bounded node, Enum node
--        , Binary node, Binary input
--        , NFData input
--        )
--     => NetworkSettings
--     -> node
--     -- ^ This node
--     -> Map node (String, String)
--     -- ^ (host, port) of nodes (Should be total including thisNode)
--     -> IO ( (Maybe input) -> IO ()
--           -- ^ Fire input event for this node (Or nothing to indicate a lack of events).
--           , Map node (Event input)
--           -- ^ Map from node to input events.
--           )









-- -- We also have a Lazy type that allows use to try and getB the value given that
-- -- we know what transaction we've completed.
-- data Lazy a
-- data TransactionId
-- -- | This will give Nothing if the value is not avilable at the end of the
-- -- transaction.
-- tryGetLazy :: TransactionId -> Lazy a -> Maybe a
-- tryGetLazy = _
-- -- Assume we have a bunch of lazy values (all player inputs) in a World record
-- data WorldInputs = WorldInputs
--     { player1InputA :: Lazy (Occ ())
--     , player1InputB :: Lazy (Occ ())
--     , player2InputA :: Lazy (Occ ())
--     , player2InputB :: Lazy (Occ ())
--     }
-- -- that we want to update in a mostly pure fashion. We take some single stream
-- -- of facts (all player input parts). These are chunked into parts
-- type Fact a = a
-- type FactStream = [[]]
