{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module Main where

import NFRP
import Simulate
import HMap as HMap
import Graphics.Gloss.Interface.IO.Game

import Safe
import Data.Typeable
import Data.Map as Map
import Data.Kind
import Data.Proxy
import Data.IORef
import Control.Monad (forM)
import Control.Monad.IO.Class (liftIO)
import Data.Time.Clock (NominalDiffTime, getCurrentTime, diffUTCTime)
import Control.Concurrent (Chan, newChan, threadDelay, writeChan, forkIO)

-- Lets make a simple calculator example with 3 clients and a server that we want to do that calculating.
data Node
    = Player
    | Bot
    deriving (Show, Read, Eq, Ord, Bounded, Enum)

instance Sing Player where
    sing _ = Player
instance Sing Bot where
    sing _ = Bot

instance ReifySomeNode Node where
    someNode Player = SomeNode (Proxy @Player)
    someNode Bot    = SomeNode (Proxy @Bot)

type Pos = (Float, Float)
data Ctx :: Node -> Type where
    Ctx :: IORef Pos -> IORef Pos -> Ctx n

allNodes :: [Node]
allNodes = [minBound..maxBound]

newCtx :: IO (Ctx node)
newCtx = Ctx
    <$> newIORef (0,0)
    <*> newIORef (0,0)

main :: IO ()
main = do
    playerCtx <- newCtx
    botCtx    <- newCtx
    let nodeCtxs = [ NodeCtx (Proxy @Player) playerCtx
                   , NodeCtx (Proxy @Bot)    botCtx
                   ]

    -- Start simulation
    (stop, circOuts, injectors) <- simulate
        circuit
        nodeCtxs
        Bot

    -- Start Bot GUI
    let botInjector = injectors HMap.! (Proxy @Bot)
        botSrcEvt = botInputDirSrcEvt $ circOuts Map.! Bot

        botAI = do
            injectEvent botInjector botSrcEvt DirUp
            threadDelay 1000000
            injectEvent botInjector botSrcEvt DirRight
            threadDelay 1000000
            injectEvent botInjector botSrcEvt DirDown
            threadDelay 1000000
            injectEvent botInjector botSrcEvt DirLeft
            threadDelay 1000000
            botAI

    forkIO botAI

    -- Start Player GUI
    playerGUI
        (700, 100)
        playerCtx
        (playerInputDirSrcEvt $ circOuts Map.! Player)
        (injectors HMap.! (Proxy @Player))

    --Stop
    stop

data CircOut = CircOut
    { playerInputDirSrcEvt :: SourceEvent Player InputDir
    , botInputDirSrcEvt    :: SourceEvent Bot    InputDir
    }

data InputDir = DirUp | DirRight | DirDown | DirLeft
    deriving (Eq, Ord, Show, Read)

playerGUI :: (Int, Int) -> Ctx myNode -> SourceEvent myNode InputDir -> EventInjector myNode -> IO ()
playerGUI windowPos (Ctx pPosIORef bPosIORef) inputDirSourceE injector = playIO
    (InWindow "NFRP Demo" (500, 500) windowPos)
    black
    60
    ()
    (\ () -> do
        playerPos <- readIORef pPosIORef
        botPos    <- readIORef bPosIORef
        return $ Pictures
            [ drawCharacter red  playerPos
            , drawCharacter blue botPos
            ]
    )
    (\ event () -> do
        case event of
            EventKey (SpecialKey sk) Down _modifiers _mousePos
                -> maybe (return ()) (injectEvent injector inputDirSourceE) $ case sk of
                    KeyUp    -> Just DirUp
                    KeyRight -> Just DirRight
                    KeyDown  -> Just DirDown
                    KeyLeft  -> Just DirLeft
                    _        -> Nothing
            _   -> return ()
        return ()
        )
    (\ dt () -> do
        -- TODO step world... do we need to do this?
        return ()
        )

drawCharacter :: Color -> Pos -> Picture
drawCharacter c (x, y) = Color c (translate x y (Circle 10))

circuit :: Moment Node Ctx CircOut
circuit = do
    (playerDirSE, playerDirE) <- newSourceEvent (Proxy @Player)
    (botDirSE   , botDirE   ) <- newSourceEvent (Proxy @Bot)

    playerPosUpdateE <- evt $ MapE dirToPos playerDirE
    playerPosB' <- beh $ Step (0,0) playerPosUpdateE
    playerPosB  <- beh $ SendB (Proxy @Player) (Proxy @[Player, Bot]) playerPosB'

    botPosUpdateE <- evt $ MapE dirToPos botDirE
    botPosB' <- beh $ Step (0,0) botPosUpdateE
    botPosB  <- beh $ SendB (Proxy @Bot) (Proxy @[Player, Bot]) botPosB'

    let bind :: forall (myNode :: Node)
             .  (Typeable myNode, IsElem myNode '[Player, Bot])
             => Proxy myNode -> Moment Node Ctx ()
        bind myNodeP = do
            listenB myNodeP playerPosB (\ (Ctx ref _) pos -> writeIORef ref pos)
            listenB myNodeP botPosB    (\ (Ctx _ ref) pos -> writeIORef ref pos)

    bind (Proxy @Player)
    bind (Proxy @Bot)

    return (CircOut playerDirSE botDirSE)

dirToPos :: InputDir -> Pos
dirToPos DirUp    = (0, 20)
dirToPos DirRight = (20, 0)
dirToPos DirDown  = (0, -20)
dirToPos DirLeft  = (-20, 0)