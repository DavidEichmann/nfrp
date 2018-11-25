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
    
import Safe
import Data.Typeable
import Data.Map as Map
import NFRP
import UI.NCurses

import Control.Monad.IO.Class (liftIO)
import Data.Time.Clock (NominalDiffTime, getCurrentTime, diffUTCTime)
import Control.Concurrent (Chan, newChan, writeChan)
import Control.Concurrent.Async
-- import System.Environment (getArgs)


-- TODO LocalInput and Node types are still hard wired into NFRP but should be moved here.

-- actuate :: forall (myNode :: Node)
--         .  (Typeable myNode, SingNode myNode)
--         => Proxy myNode                        -- What node to run.
--         -> Node                        -- Clock sync node
--         -> IO Time                     -- Local clock
--         -> Moment ()                   -- The circuit to build
--         -> Chan LocalInput             -- Local inputs
--         -> Map.Map Node (Chan [UpdateList], Chan [UpdateList])   -- (send, receive) Chanels to other nodes
--         -> IO ()
main :: IO ()
main = do

    putStrLn "Simulating all nodes..."

    t0 <- getCurrentTime
    
    let nodePairs = [ (nodeFrom, nodeTo)
                    | nodeFrom <- [minBound..maxBound]
                    , nodeTo   <- [minBound..maxBound]
                    , nodeFrom /= nodeTo]

    netChans <- Map.fromList <$> sequence 
        [ do
            c  <- newChan
            return ((nodeFrom, nodeTo), c)
        | (nodeFrom, nodeTo) <- nodePairs ]

    localInChans <- Map.fromList <$> sequence [ (node,) <$> newChan 
                                                | node <- [minBound..maxBound] ]
    
    let
        mainNode :: forall (node :: Node)
                 .  (SingNode node, Typeable node)
                 => Proxy node -> IO ()
        mainNode myNodeP
            = actuate
                myNodeP
                Server
                ((round :: NominalDiffTime -> Integer)
                    .   (* 10^(12::Int))
                    .   diffUTCTime t0
                    <$> getCurrentTime)
                calculatorCircuit
                (localInChans ! myNode)
                (Map.fromList 
                    [ (otherNode,
                        ( netChans ! (myNode, otherNode)
                        , netChans ! (otherNode, myNode)))
                    | otherNode <- [minBound..maxBound], myNode /= otherNode])
            where
                myNode = singNode myNodeP

    aClientA <- async $ mainNode (Proxy @ClientA)
    aClientB <- async $ mainNode (Proxy @ClientB)
    aClientC <- async $ mainNode (Proxy @ClientC)
    aServer  <- async $ mainNode (Proxy @Server)

    mainUI (localInChans ! ClientA)

    putStrLn "Exiting."
    return ()


mainUI :: Chan Char -> IO ()
mainUI keyInputC = runCurses $ do
    setEcho False
    w <- defaultWindow
    let mainUILoop = do
            updateWindow w $ do
                clear
                moveCursor 1 10
                drawString "Hello world!"
                moveCursor 3 10
                drawString "(press q to quit)"
                moveCursor 0 0
            render
            ev <- getEvent w (Just 15)
            case ev of
                Just (EventCharacter 'q') -> return ()
                Just (EventCharacter c) -> do
                    liftIO $ writeChan keyInputC c
                    mainUILoop
                _ -> mainUILoop

    mainUILoop


calculatorCircuit :: Moment ()
calculatorCircuit = do
    aKeyB <- (beh . (Step '0')) =<< (evt $ Source (Proxy @ClientA))
    bKeyB <- (beh . (Step '+')) =<< (evt $ Source (Proxy @ClientB))
    cKeyB <- (beh . (Step '0')) =<< (evt $ Source (Proxy @ClientC))
    
    leftB  <- beh =<< SendB (Proxy @ClientA) (Proxy @'[Server]) <$> readIntB aKeyB
    rightB <- beh =<< SendB (Proxy @ClientC) (Proxy @'[Server]) <$> readIntB cKeyB
    opB    <- beh =<< SendB (Proxy @ClientB) (Proxy @'[Server]) <$> (beh $ MapB (\case
                            '+' -> (+)
                            '/' -> div
                            '*' -> (*)
                            _   -> (-) :: (Int -> Int -> Int)) 
                        bKeyB)

    resultB_ <- beh $ opB `Ap` leftB
    _resultB  <- beh $ resultB_ `Ap` rightB

    return ()

    where
        readIntB :: Typeable o
                 => BehaviorIx o Char -> Moment (BehaviorIx o Int)
        readIntB = beh . MapB (\c -> readDef 0 [c])