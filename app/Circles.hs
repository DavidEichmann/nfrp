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

module Main where

import           Control.DeepSeq
import           Control.Monad (when)
import           Data.Binary (Binary)
import           Data.IORef
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (isJust)
import           Graphics.Gloss.Interface.IO.Game hiding (Event)
import           System.Console.CmdArgs

import           NFRP

import           Circles.Game

data CommandLineOpts = CommandLineOpts
    { node :: Maybe Player
    , latency :: Maybe Int
    , bot :: Maybe Int
    } deriving (Show, Data, Typeable)

commandLineOpts :: CommandLineOpts
commandLineOpts = CommandLineOpts
    { node = def
                &= help ("One of " ++ show [minBound..(maxBound :: Player)])
                &= typ  "NODE"
    , latency = def
                &= help ("Simulated latency in microseconds (10^-6 seconds)")
                &= typ  "MICROSEC"
    , bot = def
                &= help ("Use a bot that moves every given microseconds")
                &= typ  "MICROSEC"
    }

-- | Create source events for all players.
createSourceEvents
    :: (Binary input, NFData input)
    => NetworkSettings
    -> Player
    -- ^ Current Player.
    -> IO ( Maybe input -> IO ()
            -- ^ Fire my input event.
          , Map Player (Event input)
            -- ^ Input events of all players (including my self).
          )
createSourceEvents netSettings myNode = do
    let localhost = "127.0.0.1"
        addresses = Map.fromList
            [ (Player1, (localhost, "9001"))
            , (Player2, (localhost, "9002"))
            ]
    sourceEvents netSettings myNode addresses


main :: IO ()
main = do

    -- Choose player
    opts <- cmdArgs commandLineOpts
    myNode <- case node opts of
        Just n -> return n
        Nothing -> do
            putStrLn "Choose Player (1/2):"
            myNodeIx <- subtract 1 <$> readLn
            let myNode = [minBound..maxBound] !! myNodeIx
            putStrLn $ "You've chosen: " ++ show myNode
            return myNode

    let myNodeIx = fromEnum myNode
        windowPos = (10 + (myNodeIx * 510),10)

    -- Simulated latency
    let netSettings = maybe Default SimulateLatency (latency opts)

    -- Inputs
    (fireInput, inputs) <- createSourceEvents netSettings myNode
    let gameB = createGame inputs

    -- Bot
    case bot opts of
        Nothing -> return ()
        Just l -> do
            _ <- runBot l fireInput
            return ()

    --
    -- FRP -> IORef
    --

    -- _ <- watchB gameB print
    (_, gameIORef) <- watchLatestBIORef gameB
    let getGame = do
            (_, game) <- readIORef gameIORef
            return game

    --
    -- Game Loop
    --

    -- Initialize with no events up to time 0 (TODO this should be part of a higher lever API)
    playIO
        (InWindow "NFRP Demo" (500, 500) windowPos) black 60 ()
        -- Draw The Game
        (\ () -> drawGame <$> getGame)
        -- Input Handler
        (\ event () -> do
            -- Get inputs.
            let inputsMay = getInputsMay event

            -- We let the "World Update" function below fire the Nothing case.
            when (isJust inputsMay) (fireInput inputsMay)
        )
        -- "World Update"
        -- Note we need to call fireInput here to progress time.
        (\ _dt () -> fireInput Nothing)

drawCharacter :: Color -> Pos -> Picture
drawCharacter c (x, y) = Color c (translate x y (Circle 10))
