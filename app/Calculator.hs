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

-- Lets make a simple calculator example with 3 clients and a server that we want to do that calculating.
data Node
    = ClientA
    | ClientB
    | ClientC
    | Server
    deriving (Show, Read, Eq, Ord, Bounded, Enum)

instance Sing ClientA where
    type SingT ClientA = Node
    sing _ = ClientA
instance Sing ClientB where
    type SingT ClientB = Node
    sing _ = ClientB
instance Sing ClientC where
    type SingT ClientC = Node
    sing _ = ClientC
instance Sing Server where
    type SingT Server = Node
    sing _ = Server

allNodes :: [Node]
allNodes = [minBound..maxBound]

main :: IO ()
main = do

    putStrLn "Simulating all nodes..."

    t0 <- getCurrentTime

    let nodePairs :: [(Node, Node)]
        nodePairs = [ (nodeFrom, nodeTo)
                    | nodeFrom <- allNodes
                    , nodeTo   <- allNodes
                    , nodeFrom /= nodeTo
                    ]

    netChans :: Map.Map (Node, Node) (Chan [UpdateList Node])
        <- Map.fromList <$> sequence
            [ do
                c  <- newChan
                return ((nodeFrom, nodeTo), c)
            | (nodeFrom, nodeTo) <- nodePairs ]

    localInChans <- Map.fromList <$> sequence [ (node,) <$> newChan
                                              | node <- allNodes ]

    let
        newCtx :: IO (CtxF node)
        newCtx = Ctx <$> ((,,,)
            <$> newIORef ""
            <*> newIORef ""
            <*> newIORef ""
            <*> newIORef "")

        actuateNode :: forall (node :: Node)
                 .  (NodePC node)
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
                    | otherNode <- allNodes, myNode /= otherNode])
            where
                myNode = sing myNodeP

    aCtx <- newCtx
    stopClientA <- actuateNode (Just aCtx) (Proxy @ClientA)
    stopClientB <- actuateNode Nothing     (Proxy @ClientB)
    stopClientC <- actuateNode Nothing     (Proxy @ClientC)
    stopServer  <- actuateNode Nothing     (Proxy @Server)

    clickSomeButtons localInChans
    mainUI aCtx (localInChans ! ClientA)

    putStrLn "Exiting."

    stopClientA
    stopClientB
    stopClientC
    stopServer

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


calculatorCircuit :: Moment Node CtxF ()
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
                , Typeable n )
             => Proxy n -> Moment Node CtxF ()
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
        readIntB :: forall (o :: [Node])
                 .  GateIxC Node o Char
                 => BehaviorIx o Char -> Moment Node CtxF (BehaviorIx o Int)
        readIntB = beh . MapB (\c -> readDef 0 [c])