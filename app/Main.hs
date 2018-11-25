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

import Data.Time.Clock (NominalDiffTime, getCurrentTime, diffUTCTime)
import Control.Concurrent (newChan, forkIO)
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
    t0 <- getCurrentTime
    
    netChans <- Map.fromList <$> sequence 
        [ do
            inC  <- newChan
            outC <- newChan
            return (node, (inC, outC))
        | node <- [minBound..maxBound] ]

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
                (localInChans Map.! (singNode myNodeP))
                netChans

    _ <- forkIO $ mainNode (Proxy @ClientA)
    _ <- forkIO $ mainNode (Proxy @ClientB)
    _ <- forkIO $ mainNode (Proxy @ClientC)
    _ <- forkIO $ mainNode (Proxy @Server)
    return ()

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