{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}

module Circles.Game where

import           Control.DeepSeq
import           Data.Binary (Binary)
import           Data.Data
import           Data.Map (Map)
import qualified Data.Map as Map
import           GHC.Generics (Generic)
import           Graphics.Gloss.Interface.IO.Game hiding (Event)
import qualified Graphics.Gloss.Interface.IO.Game as Gloss

import           FRP

data Player
    = Player1
    | Player2
    deriving stock (Eq, Ord, Show, Bounded, Enum, Data, Generic)
    deriving anyclass (Binary)

type Pos = (Float, Float)

data Game = Game
    { player1Pos :: Pos
    , player2Pos :: Pos
    }
    deriving stock (Show, Read, Generic)
    deriving anyclass (Binary, NFData)

data Inputs = DirUp | DirRight | DirDown | DirLeft
    deriving stock (Eq, Ord, Show, Read, Generic)
    deriving anyclass (Binary, NFData)

-- | Game Logic
createGame
    :: Map Player (Event Inputs)
    -- ^ Input's of all players.
    -> Behavior Game
    -- ^ Game state.
createGame inputs
    = Game
        <$> inputEToPos (inputs Map.! Player1)
        <*> inputEToPos (inputs Map.! Player2)
    where
    inputEToPos :: Event Inputs -> Behavior Pos
    inputEToPos inputE = step (0, 0) ((\dir -> case dir of
                    DirLeft  -> (-delta,  0)
                    DirRight -> ( delta,  0)
                    DirUp    -> ( 0,  delta)
                    DirDown  -> ( 0, -delta)
                    ) <$> inputE)
    delta = 100

-- | Get the inputs form a Gloss Event.
getInputsMay :: Gloss.Event -> Maybe Inputs
getInputsMay event = case event of
    EventKey (SpecialKey sk) Down _modifiers _mousePos
        -> case sk of
            KeyUp    -> Just DirUp
            KeyRight -> Just DirRight
            KeyDown  -> Just DirDown
            KeyLeft  -> Just DirLeft
            _        -> Nothing
    _   -> Nothing

-- | Draw the game with Gloss.
drawGame :: Game -> Picture
drawGame (Game player1Pos' player2Pos')
    = Pictures
        [ drawCharacter red  10 player1Pos'
        , drawCharacter blue 20 player2Pos'
        ]
    where
    drawCharacter :: Color -> Float -> Pos -> Picture
    drawCharacter c size (x, y) = Color c (translate x y (thickCircle size 6))
