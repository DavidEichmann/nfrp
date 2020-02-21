{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
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
import Time
import TimeSpan
-- import Simulate
import Graphics.Gloss.Interface.IO.Game

-- import Data.Map as Map
import Data.Time.Clock
import Data.IORef
-- import Control.Monad (forM_)
-- import Control.Concurrent (threadDelay, forkIO)

data Game = Game
    { playerPos :: Pos
    }

data InputDir = DirUp | DirRight | DirDown | DirLeft
    deriving (Eq, Ord, Show, Read)

main :: IO ()
main = do
    --
    -- FRP
    --

    -- Inputs
    (fireInput, inputE) <- sourceEvent

    -- Game Logic
    let playerPosB :: Behavior Pos
        playerPosB = step (0, 0) ((\dir -> case dir of
                    DirLeft  -> (-delta,  0)
                    DirRight -> ( delta,  0)
                    DirUp    -> ( 0,  delta)
                    DirDown  -> ( 0, -delta)
                    ) <$> inputE)
        delta = 100

    --
    -- FRP -> IORef
    --

    _ <- watchB playerPosB print
    (_, playerPosIORef) <- watchLatestBIORef playerPosB
    let getGame = do
            (_, playerPos') <- readIORef playerPosIORef
            return (Game playerPos')

    --
    -- Game Loop
    --

    gameStartTime <- getCurrentTime
    let getGameTime = do
            t <- getCurrentTime
            let dt = t `diffUTCTime` gameStartTime
                dtns = floor (1000000 * dt)
            return dtns

    -- Initialize with no events up to time 0 (TODO this should be part of a higher lever API)
    fireInput (listToEPartsExcInc Nothing (Just 0) [])
    lastUpdateTimeIORef :: IORef Time <- newIORef 0
    playIO
        (InWindow "NFRP Demo" (500, 500) (100, 100))
        black
        60
        ()
        -- Draw The Game
        (\ () -> do
            game <- getGame
            return $ Pictures
                [ drawCharacter red (playerPos game)
                ]
        )
        -- Fire Input Events
        (\ event () -> do
            t <- getGameTime
            lastUpdateTime <- readIORef lastUpdateTimeIORef

            -- Get inputs.
            let inputsMay = case event of
                    EventKey (SpecialKey sk) Down _modifiers _mousePos
                        -> case sk of
                            KeyUp    -> Just DirUp
                            KeyRight -> Just DirRight
                            KeyDown  -> Just DirDown
                            KeyLeft  -> Just DirLeft
                            _        -> Nothing
                    _   -> Nothing

            fireInput $ listToEPartsExcInc (Just lastUpdateTime) (Just t)
                            [(t, inputs) | Just inputs <- [inputsMay]]
            writeIORef lastUpdateTimeIORef t
        )
        (\ _dt () ->
            -- TODO step world... do we need to do this?
            return ()
            )

drawCharacter :: Color -> Pos -> Picture
drawCharacter c (x, y) = Color c (translate x y (Circle 10))

type Pos = (Float, Float)

{-}
-- Lets make a simple calculator example with 3 clients and a server that we want to do that calculating.
data Node
    = Player
    | Bot
    deriving (Show, Read, Eq, Ord, Bounded, Enum)

instance Sing Player where
    sing _ = Player
instance Sing Bot where
    sing _ = Bot


data Ctx = Ctx (IORef Pos) (IORef Pos)

type MT = MomentTypes Node Ctx

type Mom a = Moment MT a

allNodes :: [Node]
allNodes = [minBound..maxBound]

newCtx :: IO Ctx
newCtx = Ctx
    <$> newIORef (0,0)
    <*> newIORef (0,0)

main :: IO ()
main = do
    playerCtx <- newCtx
    botCtx    <- newCtx
    let nodeCtxs = [ NodeCtx Player playerCtx
                   , NodeCtx Bot    botCtx
                   ]

    -- Start simulation
    (stop, circOuts, injectors, clocks) <- simulate
        circuit
        nodeCtxs
        Bot

    -- Start Bot GUI
    let botInjector = injectors Map.! Bot
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

    _ <- forkIO botAI

    -- Start Player GUI
    playerGUI
        (700, 100)
        playerCtx
        (playerInputDirSrcEvt $ circOuts Map.! Player)
        (injectors Map.! Player)
        (clocks Map.! Player)

    --Stop
    stop

data CircOut = CircOut
    { playerInputDirSrcEvt :: SourceEvent Node InputDir -- Player
    , botInputDirSrcEvt    :: SourceEvent Node InputDir -- Bot
    }

playerGUI :: (Eq node, Show node)
          => (Int, Int)
          -> Ctx
          -> SourceEvent node InputDir
          -> EventInjector node
          -> IO Time
          -> IO ()
playerGUI windowPos (Ctx pPosIORef bPosIORef) inputDirSourceE injector _getTime = playIO
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
    (\ _dt () ->
        -- TODO step world... do we need to do this?
        return ()
        )

circuit :: Mom CircOut
circuit = do
    (playerDirSE, playerDirE) <- newSourceEvent Player
    (botDirSE   , botDirE   ) <- newSourceEvent Bot

    playerPosB
        <- beh
        . sendBAll Player
        . step (0,0)
        $ dirToPos <$> playerDirE

    botPosB
        <- beh
        . sendBAll Bot
        . step (0,0)
        $ dirToPos <$> botDirE

    pDir  <- beh $ step  DirUp playerDirE
    pDirD <- beh $ delay DirUp pDir
    pDirBothB    <- beh $ (,) <$> pDir <*> pDirD
    pDirBothOnEB <- beh
                    . step Nothing
                    $ sample (\ valB _valE -> Just valB) pDirBothB playerDirE

    listenB Player pDirBothB    (\ _ a _ -> putStrLn $ "@@@ Expecting same: " ++ show a)
    listenB Player pDirBothOnEB (\ _ a _ -> putStrLn $ "@@@ Expecting diff: " ++ show a)

    let bind ::Node -> Mom ()
        bind node = do
            listenB node playerPosB (\ (Ctx ref _) pos _ -> writeIORef ref pos)
            listenB node botPosB    (\ (Ctx _ ref) pos _ -> writeIORef ref pos)

    bind Player
    bind Bot

    return (CircOut playerDirSE botDirSE)

dirToPos :: InputDir -> Pos
dirToPos DirUp    = (0, 20)
dirToPos DirRight = (20, 0)
dirToPos DirDown  = (0, -20)
dirToPos DirLeft  = (-20, 0)

-- movementControler :: EventIx os (InputDir, KeyState) -> Mom (BehaviorIx os (Time -> Pos))
-- movementControler inDirE = do
--     activeDirsB :: BehaviorIx os [InputDir]
--         <- (beh $ Step []) <$> fmap (\ () -> _) inDirE

--     _

-}