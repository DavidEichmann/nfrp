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

import Data.Kind
import Data.IORef
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
    
    lhsRef :: IORef String <- newIORef ""
    opRef  :: IORef String <- newIORef ""
    rhsRef :: IORef String <- newIORef ""
    totRef :: IORef String <- newIORef ""
    
    let
        ctx :: CtxF node
        ctx = Ctx
            ( lhsRef
            , opRef
            , rhsRef
            , totRef
            )

        mainNode :: forall (node :: Node)
                 .  (SingNode node, Typeable node)
                 => Proxy node -> IO ()
        mainNode myNodeP
            = actuate
                ctx
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

    mainUI ctx (localInChans ! ClientA)

    putStrLn "Exiting."
    return ()

type Ctx    = (IORef String, IORef String, IORef String, IORef String)
data CtxF :: Node -> Type where
    Ctx :: Ctx -> CtxF n

mainUI :: CtxF n -> Chan Char -> IO ()
mainUI (Ctx (lhsRef, opRef, rhsRef, totRef)) keyInputC = runCurses $ do
    setEcho False
    w <- defaultWindow
    let mainUILoop = do
            lhs <- liftIO $ readIORef lhsRef
            op  <- liftIO $ readIORef opRef
            rhs <- liftIO $ readIORef rhsRef
            tot <- liftIO $ readIORef totRef
            updateWindow w $ do
                clear
                moveCursor 1 10
                drawString $ lhs ++ " " ++ op ++ " " ++ rhs ++ " = " ++ tot
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


calculatorCircuit :: Moment CtxF ()
calculatorCircuit = do
    aKeyB <- (beh . (Step '0')) =<< (evt $ Source (Proxy @ClientA))
    bKeyBLocal <- (beh . (Step '+')) =<< (evt $ Source (Proxy @ClientB))
    cKeyB <- (beh . (Step '0')) =<< (evt $ Source (Proxy @ClientC))
    
    opCharB <- beh
             . SendB (Proxy @ClientB) (Proxy @'[Server, ClientA, ClientB, ClientC])
             $ bKeyBLocal


    leftB  <- beh =<< SendB (Proxy @ClientA) (Proxy @'[Server, ClientA, ClientB, ClientC]) <$> readIntB aKeyB
    rightB <- beh =<< SendB (Proxy @ClientC) (Proxy @'[Server, ClientA, ClientB, ClientC]) <$> readIntB cKeyB
    opB    <- beh =<< SendB (Proxy @ClientB) (Proxy @'[Server, ClientA, ClientB, ClientC]) <$> (beh $ MapB (\case
                            '+' -> (+)
                            '/' -> div
                            '*' -> (*)
                            _   -> (-) :: (Int -> Int -> Int)) 
                        opCharB)

    resultB_ <- beh $ opB `Ap` leftB
    totalB   <- beh $ resultB_ `Ap` rightB

    let bind :: forall (ns :: '[Node])
             .  IsSubsetEq ns '[Server, ClientA, ClientB, ClientC]
             => Proxy ns -> Moment CtxF ()
        bind listenNodeP = do
            listenB listenNodeP leftB   (\(Ctx (r,_,_,_)) -> writeIORef r . show)
            listenB listenNodeP opCharB (\(Ctx (_,r,_,_)) -> writeIORef r . show)
            listenB listenNodeP rightB  (\(Ctx (_,_,r,_)) -> writeIORef r . show)
            listenB listenNodeP totalB  (\(Ctx (_,_,_,r)) -> writeIORef r . show)
    bind (Proxy @'[ClientA, ClientB, ClientC])

    return ()

    where
        readIntB :: Typeable o
                 => BehaviorIx o Char -> Moment CtxF (BehaviorIx o Int)
        readIntB = beh . MapB (\c -> readDef 0 [c])