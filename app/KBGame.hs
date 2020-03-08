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

module Main where

import KnowledgeBase

main :: IO ()
main = putStrLn "Hello World!"

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

gameLogic :: GameDefinition Game
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

-- TODO use generics to do this. Why do this like this? Well we'll need to send
-- facts over the network eventually, and we'll need a way to index those facts
-- on their corresponding field, so something like this seems inherently
-- necessary.
instance FieldIx Game where
    fieldIxs = Game
        { player1InputA         = EIx 0
        , player1InputB         = EIx 1
        , player2InputA         = EIx 2
        , player2InputB         = EIx 3
        , player1Pos            = BIx 4
        , player2Pos            = BIx 5
        , arePlayersOverlapping = BIx 6
        }
