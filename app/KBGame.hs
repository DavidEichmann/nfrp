{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Main where

import qualified GHC.Generics as GHC
import Generics.SOP

import KnowledgeBase

main :: IO ()
main = do
    let kb = newKnowledgeBase gameLogic
        player1InputAFacts = facts player1InputA Nothing Nothing [ (1, ()), (10, ()), (100, ())]
        player1InputBFacts = facts player1InputB Nothing Nothing [ (1, ()), (5, ()), (50, ())]
        kb' = insertFacts (player1InputAFacts ++ player1InputBFacts) kb
    print $ kb'

-- Describes all the data E/Bs of the game (and inputs)
data Game (f :: GameData) = Game
    { player1InputA          :: SE Game f ()
    , player1InputB          :: SE Game f ()
    , player2InputA          :: SE Game f ()
    , player2InputB          :: SE Game f ()
    , player1Pos             :: B Game f Pos
    , player2Pos             :: B Game f Pos
    , arePlayersOverlapping  :: B Game f Bool
    }
    deriving stock (GHC.Generic)
    deriving anyclass (Generic, FieldIx)

type Pos = (Int, Int)

gameLogic :: Game 'Definition
gameLogic = Game
    { player1InputA = sourceEventDef
    , player1InputB = sourceEventDef
    , player2InputA = sourceEventDef
    , player2InputB = sourceEventDef
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
