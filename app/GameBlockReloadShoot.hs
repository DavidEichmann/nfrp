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

import qualified Graphics.Gloss.Interface.Pure.Game as Gloss
import           Graphics.Gloss.Interface.Pure.Game hiding (Event)
import           Generics.SOP
import qualified GHC.Generics as GHC

import qualified ReactiveData as RD
import           ReactiveData
import           Safe (headMay)
import           Debug.Trace

data Game f = Game
    { player1Input_Move   :: SourceEvent f Move
    , player2Input_Move   :: SourceEvent f Move
    , state :: Value f State
    } deriving (GHC.Generic, Generic, FieldIx)

deriving instance Show (Game 'Values)

type Value f a = RD.V Game f a
type Event f a = RD.E Game f a
type SourceEvent f a = RD.SE Game f a

data PlayerData
    = PlayerData
        Int -- Score
        Int -- Amo
        (Maybe Move) -- queued move
    deriving (Show)

data State = State
    PlayerData -- Player1
    PlayerData -- Plater2
    deriving (Show)

data Move
    = Block
    | Reload
    | TryShoot
    deriving (Show)

game0 :: KnowledgeBase
game0 = mkKnowledgeBase Game
    { player1Input_Move = sourceEvent
    , player2Input_Move = sourceEvent
    , state = value (State (PlayerData 0 0 Nothing) (PlayerData 0 0 Nothing)) $ do
        State
            p1Data@(PlayerData p1Score p1Amo p1MoveQ)
            p2Data@(PlayerData p2Score p2Amo p2MoveQ)
            <- prevV state
        p1MoveOcc <- getE player1Input_Move
        p2MoveOcc <- getE player2Input_Move

        let -- Player 1 wins
            applyMoves TryShoot Reload | p1Amo > 0 = State
                (PlayerData (p1Score+1) 0 Nothing)
                (PlayerData p2Score     0 Nothing)
            -- Player 2 wins
            applyMoves Reload TryShoot | p2Amo > 0 = State
                (PlayerData p1Score     0 Nothing)
                (PlayerData (p2Score+1) 0 Nothing)
            -- No winner yet
            applyMoves move1 move2 = State
                (PlayerData p1Score (amo' p1Amo move1) Nothing)
                (PlayerData p2Score (amo' p2Amo move2) Nothing)
                where
                amo' amo move = case move of
                    Reload   -> amo + 1
                    TryShoot -> max 0 (amo - 1)
                    Block    -> amo

        return $ case (p1MoveOcc, p2MoveOcc) of
            (NoOcc, NoOcc) -> NoOcc
            (Occ p1Move, Occ p2Move) -> Occ (applyMoves p1Move p2Move)
            (Occ p1Move, NoOcc) -> case p2MoveQ of
                Nothing -> Occ (State (PlayerData p1Score p1Amo (Just p1Move)) p2Data)
                Just p2Move -> Occ (applyMoves p1Move p2Move)
            (NoOcc, Occ p2Move) -> case p1MoveQ of
                Nothing -> Occ (State p1Data (PlayerData p2Score p2Amo (Just p2Move)))
                Just p1Move -> Occ (applyMoves p1Move p2Move)

    }

drawGame :: Game 'Values -> Picture
drawGame Game { state = F s@(State
            (PlayerData p1Score p1Amo p1MoveQ)
            (PlayerData p2Score p2Amo p2MoveQ))
        }
    = traceShow s $ Pictures $ concat
        [ [color white $ text $ (show p1Score ++ "-" ++ show p2Score)
          ]
        ]

-- | Get the inputs from a Gloss Event.
getInputs :: [Gloss.Event] -> Game 'SourceEvents
getInputs glossEvents = Game
    { state     = F ()

    , player1Input_Move = F $ headMay [ m | k <- keyDowns, Just m <- [lookup k
            [ (Char 'a', Block)
            , (Char 's', Reload)
            , (Char 'd', TryShoot)
            ]]]

    , player2Input_Move = F $ headMay [ m | k <- keyDowns, Just m <- [lookup k
            [ (SpecialKey KeyLeft , Block)
            , (SpecialKey KeyDown , Reload)
            , (SpecialKey KeyRight, TryShoot)
            ]]]
    }
    where
    keyDowns = [ k | EventKey k Down _modifiers _mousePos <- glossEvents ]

main :: IO ()
main = play
        (InWindow "NFRP Demo" (500, 500) (10, 10))
        black
        10
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
