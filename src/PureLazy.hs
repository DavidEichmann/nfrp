{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
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

module PureLazy where

import Control.Concurrent.STM
import Control.Exception
import Data.Either (isRight)
import Data.Maybe (isJust)

-- | Overall we want a generic ish system such that we can specify state
-- transisions in a simple format. This is be expressed as a state type...

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

stepGame :: Game Sample -> Game Definition
stepGame gamePrev = define $ \ gameCurr ->  Game
    -- Source Inputs need no update
    { player1InputA = Source
    , player1InputB = Source
    , player2InputA = Source
    , player2InputB = Source
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
    , arePlayersOverlapping = behaviour $ do
        p1 <- getB $ player1Pos gameCurr
        p2 <- getB $ player2Pos gameCurr
        return (p1 == p2)
    }

-- | withCurrent is like fix in that it allows you to refer to the current state.
define :: (game Symbolic -> game Definition) -> game Definition
define = _

-- | Fold a behaviour from and initial value and some updates
foldB :: a -> BMonad (Update a) -> BDefinition a
foldB = _

-- | Define a behaviour
behaviour :: BMonad a -> BDefinition a
behaviour = _

-- | Used in a step funciton to indicate this value is a source event.
data Source = Source

-- | Sample represents a snapshot of the game state at a given time. In stepGame,
-- gamePrev implicitly represents the snapshot of the game just before this
-- step (i.e. the previous state).
data Sample

-- | Think of this as a symbolic version of Sample where the values are wrapped.
data Symbolic

-- | Defines how a type is stepped and also its initial values
data Definition

-- | Wraps behaviors in the state type.
type family B f a where
    B Sample     a = a
    B Symbolic   a = SymbolB a
    B Definition a = BDefinition a

-- | Wraps source events in the state type.
type family SE f a where
    SE Sample     a = Occ a
    SE Symbolic   a = SymbolE a
    SE Definition a = Source

-- | Used to build a behaviour
data BMonad a
instance Functor BMonad where -- TODO
instance Applicative BMonad where -- TODO
instance Monad BMonad where -- TODO
getB :: SymbolB a -> BMonad a
getB = _
getE :: SymbolE a -> BMonad (Maybe a)
getE = _

-- | Definition of a single behaviour
data BDefinition a

-- | If a behaviour should be updated or remain the same
data Update a = Update a | NoUpdate

-- An event occurence. We can generally think of `Event`s as Behaviours of Occ
-- that are only an Occ at the time the event occurs.
-- TODO!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! We must take special care
-- that Occ can't be directly created, else the programmer will likely create a
-- non instantaneous event.
data Occ a = NoOcc | Occ a

-- | A symbolic value
data SymbolB a
data SymbolE a

data TODO

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
