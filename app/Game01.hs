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
import Generics.SOP
import qualified GHC.Generics as GHC

import qualified ReactiveData as RD
import           ReactiveData
import Safe (headMay)

data Game f = Game
    { playerPos       :: Value f Pos
    , score           :: Value f Int
    , targetPos       :: Value f (Maybe Pos) -- Current target
    , targetPosRest   :: Value f [Pos]  -- future targets
    , targetHit       :: Event f Pos -- Player reaches the target
    , inputClickLeft  :: SourceEvent f ()
    , inputClickRight :: SourceEvent f ()
    , inputClickUp    :: SourceEvent f ()
    , inputClickDown  :: SourceEvent f ()
    } deriving (GHC.Generic, Generic, FieldIx)

type Value f a = RD.V Game f a
type Event f a = RD.E Game f a
type SourceEvent f a = RD.SE Game f a

targets :: [Pos]
targets =
    [(d*x,d*y) | (x,y) <-
        [ (5, 3)
        , (5, 5)
        , (0, 3)
        , (-2, -3)
        ]
    ]

d :: Float
d = 20

game0 :: KnowledgeBase
game0 = mkKnowledgeBase Game

    { playerPos = value (0, 0) $ do
        Occ dPos <- foldOccs plusPos <$> sequence
            [ ((-d, 0) <$) <$> getE inputClickLeft
            , (( d, 0) <$) <$> getE inputClickRight
            , (( 0, d) <$) <$> getE inputClickUp
            , (( 0,-d) <$) <$> getE inputClickDown
            ]
        pos <- prevV playerPos
        return $ Occ (plusPos pos dPos)

    , score = value 0 $ do
        Occ _ <- getE targetHit
        pScore <- prevV score
        return (Occ (pScore + 1))

    , targetPos = value (Just (head targets)) $ do
        Occ _ <- getE targetHit
        nextTargets <- prevV targetPosRest
        return (Occ (headMay nextTargets))

    , targetPosRest = value (tail targets) $ do
        Occ _ <- getE targetHit
        nextTargets <- prevV targetPosRest
        return (Occ (drop 1 nextTargets))

    , targetHit = event $ do
        Occ pos <- changeE playerPos
        pTargetPos <- prevV targetPos
        return $ if Just pos == pTargetPos
            then Occ pos
            else NoOcc

    , inputClickLeft  = sourceEvent
    , inputClickRight = sourceEvent
    , inputClickUp    = sourceEvent
    , inputClickDown  = sourceEvent
    }

type Pos = (Float, Float)

plusPos :: Pos -> Pos -> Pos
plusPos (x,y) (a,b) = (x+a,y+b)

drawGame :: Game 'Values -> Picture
drawGame game
    = Pictures $ concat
        [ [drawCharacter red (unF $ playerPos game)]
        , [drawCharacter yellow tpos | F (Just tpos) <- [targetPos game]]
        , [color white $ text (show $ unF $ score game)]
        ]

-- | Get the inputs from a Gloss Event.
getInputs :: [Gloss.Event] -> Game 'SourceEvents
getInputs glossEvents = Game
    { playerPos       = F ()
    , score           = F ()
    , targetPos       = F ()
    , targetPosRest   = F ()
    , targetHit       = F ()
    , inputClickLeft  = F $ if elem (SpecialKey KeyLeft)  keyDowns then Just () else Nothing
    , inputClickRight = F $ if elem (SpecialKey KeyRight) keyDowns then Just () else Nothing
    , inputClickUp    = F $ if elem (SpecialKey KeyUp)    keyDowns then Just () else Nothing
    , inputClickDown  = F $ if elem (SpecialKey KeyDown)  keyDowns then Just () else Nothing
    }
    where
    keyDowns = [ k | EventKey k Down _modifiers _mousePos <- glossEvents ]

main :: IO ()
main = play
        (InWindow "NFRP Demo" (500, 500) (10, 10))
        black
        30
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
