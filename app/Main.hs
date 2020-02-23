{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module Main where

main :: IO ()
main = putStrLn "TODO"

{-}
import NFRP
import Simulate

import Data.Map as Map
import Control.Monad.IO.Class
-- import Control.Concurrent (threadDelay, forkIO)

import Graphics.UI.Gtk as UI

-- Lets make a simple calculator example with 3 clients and a server that we want to do that calculating.
data Node
    = Server
    | ClientA
    | ClientB
    deriving (Show, Read, Eq, Ord, Bounded, Enum)
type B a = Behavior Node a
type E a = Event    Node a

data Ctx = Ctx

type MT = MomentTypes Node Ctx
type Mom a = Moment MT a

allNodes :: [Node]
allNodes = [minBound..maxBound]

newCtx :: IO Ctx
newCtx = return Ctx

-- data Model = Model
--     { workers :: B [Node]   -- Server
--     , isWorkingA :: B Bool  -- ClinetA
--     , isWorkingB :: B Bool  -- ClinetB
--     }

main :: IO ()
main = mdo
    -- Build FRP model
    let circuit = do
            -- Clients only have source events
            (isWorkingASE, isWorkingAE) <- newSourceEvent ClientA
            (isWorkingBSE, isWorkingBE) <- newSourceEvent ClientB
            isWorkingA <- beh $ step False isWorkingAE
            isWorkingB <- beh $ step False isWorkingBE

            -- Send Source events to server
            isWorkingA'Server <- beh $ sendB ClientA [Server] isWorkingA
            isWorkingB'Server <- beh $ sendB ClientB [Server] isWorkingB

            -- Server creates a list of working clients.
            workersBeh <- beh
                    $   (++)
                    <$> fmap (\iwa -> [ClientA | iwa]) isWorkingA'Server
                    <*> fmap (\iwb -> [ClientB | iwb]) isWorkingB'Server

            listenB Server workersBeh (\ _ workers t -> do
                putStrLn $ "@@@ BAM! " ++ show t ++ ": " ++ show workers
                labelSetText workersLabel' (show workers))

            return (Map.fromList
                [ (ClientA, isWorkingASE)
                , (ClientB, isWorkingBSE)
                ])

    -- Start simulation
    serverCtx  <- newCtx
    clientACtx <- newCtx
    clientBCtx <- newCtx
    let nodeCtxs = [ NodeCtx Server  serverCtx
                   , NodeCtx ClientA clientACtx
                   , NodeCtx ClientB clientBCtx
                   ]

    (stop, circOuts, injectors, _clocks) <- simulate
        circuit
        nodeCtxs
        Server

    -- Start GUI
    workersLabel' <- do
        _ <- initGUI
        win <- windowNew
        set win [ windowTitle := "BAM!"
                , windowDefaultWidth  := 200
                , windowDefaultHeight := 400
                ]
        grid <- gridNew
        gridSetRowHomogeneous grid True
        workersLabel <- labelNew (Just "[]")
        let mkBtn node = do
                b <- checkButtonNewWithLabel (show node)
                _ <- b `on` toggled $ injectEvent
                        (injectors Map.! node)
                        (circOuts Map.! node Map.! node)
                        =<< toggleButtonGetActive b
                return b
        btnA <- mkBtn ClientA
        btnB <- mkBtn ClientB
        gridAttach grid workersLabel 0 0 1 1
        gridAttach grid btnA 0 1 1 1
        gridAttach grid btnB 0 2 1 1
        containerAdd win grid
        _ <- win `on` deleteEvent $ do
            liftIO mainQuit
            return False
        widgetShowAll win
        return workersLabel
    mainGUI

    -- Stop the FRP.
    stop

-}