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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}

module Game01 where

import           Data.Proxy (Proxy(..))
import qualified Graphics.Gloss.Interface.Pure.Game as Gloss
import           Graphics.Gloss.Interface.Pure.Game hiding (Event)
import Generics.SOP
import qualified GHC.Generics as GHC

import qualified ReactiveData as RD
import           ReactiveData

data Game f = Game
    { playerPos       :: Value f Pos
    , inputClickLeft  :: SourceEvent f ()
    , inputClickRight :: SourceEvent f ()
    , inputClickUp    :: SourceEvent f ()
    , inputClickDown  :: SourceEvent f ()
    } deriving (GHC.Generic, Generic, FieldIx)

type Value f a = RD.V Game f a
type Event f a = RD.E Game f a
type SourceEvent f a = RD.SE Game f a

game0 :: KnowledgeBase
game0 = mkKnowledgeBase Game
    { playerPos = value (0, 0) $ do
        -- return $ Occ (1, 2)
        Occ dPos <- foldOccs plusPos <$> sequence
            [ ((-1, 0) <$) <$> getE inputClickLeft
            , (( 1, 0) <$) <$> getE inputClickRight
            , (( 0, 1) <$) <$> getE inputClickUp
            , (( 0,-1) <$) <$> getE inputClickDown
            ]
        pos <- prevV playerPos
        return $ Occ (plusPos pos dPos)

    , inputClickLeft  = sourceEvent
    , inputClickRight = sourceEvent
    , inputClickUp    = sourceEvent
    , inputClickDown  = sourceEvent
    }

type Pos = (Float, Float)

plusPos :: Pos -> Pos -> Pos
plusPos (x,y) (a,b) = (x+a,y+b)

drawGame :: Game 'Raw -> Picture
drawGame game
    = Pictures
        [ drawCharacter red (unF $ playerPos game)
        ]

-- | Get the inputs from a Gloss Event.
getInputs :: [Gloss.Event] -> Game 'SourceEvents
getInputs glossEvents = Game
    { playerPos = Field ()
    , inputClickLeft  = Field $ if elem (SpecialKey KeyLeft)  keyDowns then Just () else Nothing
    , inputClickRight = Field $ if elem (SpecialKey KeyRight) keyDowns then Just () else Nothing
    , inputClickUp    = Field $ if elem (SpecialKey KeyUp)    keyDowns then Just () else Nothing
    , inputClickDown  = Field $ if elem (SpecialKey KeyDown)  keyDowns then Just () else Nothing
    }
    where
    keyDowns = [ k | EventKey k Down _modifiers _mousePos <- glossEvents ]

main :: IO ()
main = play
        (InWindow "NFRP Demo" (500, 500) (10, 10))
        black
        60
        (game0, [], 0 :: Time)
        -- Draw The Game
        (\ (gameKb, _, tCurr) -> drawGame $ getLatestPerField (Proxy @Game) tCurr gameKb)
        -- Input Handler
        (\ glossEvent (gameKb, gEventQ, tPrev) -> (gameKb, glossEvent:gEventQ, tPrev))
        -- "World Update"
        (\ dt (gameKb, gventQ, tPrev) -> let tCurr = tPrev + (floor $ dt * 100000) in
            ( progressKB tPrev tCurr (getInputs gventQ) gameKb
            , []
            , tCurr
            )
        )

drawCharacter :: Color -> Pos -> Picture
drawCharacter c (x, y) = Color c (translate x y (Circle 10))
