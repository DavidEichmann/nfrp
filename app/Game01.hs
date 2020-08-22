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

module Game01 where

import           Control.DeepSeq
import           Control.Monad (when)
import           Data.Binary (Binary)
import           Data.IORef
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (isJust)
import qualified Graphics.Gloss.Interface.Pure.Game as Gloss
import           Graphics.Gloss.Interface.Pure.Game hiding (Event)
import           System.Console.CmdArgs

import qualified ReactiveData as RD
import           ReactiveData hiding (Value, Event, SourceEvent)

data Game f = Game
    { playerPos       :: Value f Pos
    , inputClickLeft  :: SourceEvent f ()
    , inputClickRight :: SourceEvent f ()
    , inputClickUp    :: SourceEvent f ()
    , inputClickDown  :: SourceEvent f ()
    }

type Value f a = RD.Value Game f a
type Event f a = RD.Event Game f a
type SourceEvent f a = RD.SourceEvent Game f a

game0 = mkKnowledgeBase Game
    { playerPos = ValueDef 0 $ do
        Occ dPosE <- foldOccs plusPos <$> sequence
            [ (-1, 0) <$ getE inputClickLeft
            , ( 1, 0) <$ getE inputClickRight
            , ( 0, 1) <$ getE inputClickUp
            , ( 0,-1) <$ getE inputClickDown
            ]
        pos <- prevV playerXPos
        return (plusPos pos dPos)

    , inputClickLeft  = SourceEvent
    , inputClickRight = SourceEvent
    , inputClickUp    = SourceEvent
    , inputClickDown  = SourceEvent
    }

type Pos = (Float, Float)
plusPos (x,y) (a,b) = (x+a,y+b)

drawGame :: Game 'Raw -> Picture
drawGame game
    = Pictures
        [ drawCharacter red  10 (playerPos game)
        ]

-- | Get the inputs from a Gloss Event.
getInputs :: [Gloss.Event] -> Game _
getInputs event = gameNoE
    { inputClickLeft  = elem (SpecialKey KeyLeft)  keyDowns
    , inputClickRight = elem (SpecialKey KeyRight) keyDowns
    , inputClickUp    = elem (SpecialKey KeyUp)    keyDowns
    , inputClickDown  = elem (SpecialKey KeyDown)  keyDowns
    }
    where
    keyDowns = [ k | EventKey k Down _modifiers _mousePos <- event ]

main :: IO ()
main = play
        (InWindow "NFRP Demo" (500, 500) windowPos)
        black
        60
        (game0, [], 0)
        -- Draw The Game
        (\ (gameKb, _, _) -> drawGame <$> getLatestPerField gameKb)
        -- Input Handler
        (\ event (gameKb, gEventQ, tPrev) -> (gameKb, event:gEventQ, tPrev))
        -- "World Update"
        (\ dt (gameKb, gventQ, tPrev) -> let tCurr = tPrev + dt in
            ( progressKB tPrev tCurr (getInputs gventQ)
            , []
            , tCurr
            )
        )

drawCharacter :: Color -> Pos -> Picture
drawCharacter c (x, y) = Color c (translate x y (Circle 10))
