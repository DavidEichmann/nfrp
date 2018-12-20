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
import Control.Concurrent (Chan, newChan, threadDelay, writeChan)
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
                    , nodeFrom /= nodeTo
                    ]

    netChans <- Map.fromList <$> sequence
        [ do
            c  <- newChan
            return ((nodeFrom, nodeTo), c)
        | (nodeFrom, nodeTo) <- nodePairs ]

    localInChans <- Map.fromList <$> sequence [ (node,) <$> newChan
                                              | node <- [minBound..maxBound] ]

    let
        newCtx :: IO (CtxF node)
        newCtx = Ctx <$> ((,,,)
            <$> newIORef ""
            <*> newIORef ""
            <*> newIORef ""
            <*> newIORef "")

        actuateNode :: forall (node :: Node)
                 .  (SingNode node, Typeable node)
                 => Maybe (CtxF node) -> Proxy node -> IO (IO ())
        actuateNode ctxMay myNodeP = do
            ctx <- maybe newCtx return ctxMay
            actuate
                ctx
                myNodeP
                Server
                ((round :: NominalDiffTime -> Integer)
                    .   (* 10^(12::Int))
                    .   flip diffUTCTime t0
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

    aCtx <- newCtx
    stopClientA <- actuateNode (Just aCtx) (Proxy @ClientA)
    stopClientB <- actuateNode Nothing     (Proxy @ClientB)
    stopClientC <- actuateNode Nothing     (Proxy @ClientC)
    stopServer  <- actuateNode Nothing     (Proxy @Server)

    inputGenAsync <- async (clickSomeButtons localInChans)
    mainUI aCtx (localInChans ! ClientA)

    _ <- wait inputGenAsync
    stopClientA
    stopClientB
    stopClientC
    stopServer

    putStrLn "Exiting."
    return ()

type Ctx    = (IORef String, IORef String, IORef String, IORef String)
data CtxF :: Node -> Type where
    Ctx :: Ctx -> CtxF n

clickSomeButtons :: Map.Map Node (Chan Char) -> IO ()
clickSomeButtons chans = do
    let send node char = do
            threadDelay (100000 `div` 2)
            writeChan (chans Map.! node) char
    send ClientA '9'
    send ClientB '+'
    send ClientC '4'
    send ClientB '-'

    return ()

mainUI :: CtxF n -> Chan Char -> IO ()
mainUI (Ctx (lhsRef, opRef, rhsRef, totRef)) keyInputC = runCurses $ do
    setEcho False
    w <- defaultWindow
    let mainUILoop = do
            lhs <- ("lol" ++) <$> (liftIO $ readIORef lhsRef)
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

    let bind :: ( IsElem n '[Server, ClientA, ClientB, ClientC]
                , Typeable n
                , SingNode n )
             => Proxy n -> Moment CtxF ()
        bind listenNodeP = do
            listenB listenNodeP leftB   (\(Ctx (r,_,_,_)) -> writeIORef r . show)
            listenB listenNodeP opCharB (\(Ctx (_,r,_,_)) -> writeIORef r . show)
            listenB listenNodeP rightB  (\(Ctx (_,_,r,_)) -> writeIORef r . show)
            listenB listenNodeP totalB  (\(Ctx (_,_,_,r)) -> writeIORef r . show)
    bind (Proxy @ClientA)
    bind (Proxy @ClientB)
    bind (Proxy @ClientC)

    return ()

    where
        readIntB :: (SingNodes o, Typeable o)
                 => BehaviorIx o Char -> Moment CtxF (BehaviorIx o Int)
        readIntB = beh . MapB (\c -> readDef 0 [c])