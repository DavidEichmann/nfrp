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

module Simulate (simulate) where

import Safe
import Data.Typeable
import Data.Map ((!))
import qualified Data.Map as Map
import NFRP

import Data.Kind
import Data.IORef
import Control.Monad.IO.Class (liftIO)
import Data.Time.Clock (NominalDiffTime, getCurrentTime, diffUTCTime)
import Control.Concurrent (Chan, newChan, threadDelay, writeChan)

data NodeCtxMay node (ctxF :: node -> Type)
  = forall (myNode :: node) . NodePC myNode => NodeCtxMay (Proxy myNode) (Maybe (ctxF myNode))

simulate :: forall (node :: Type) (ctxF :: node -> Type)
         .  (NodeC node)
         => Moment node ctxF ()        -- ^ ciruit to simulate
         -> [NodeCtxMay node ctxF]                -- ^ nodes  to simulate
         -> node                  -- ^ clockSyncNode
         -> IO ()
simulate circuitM allNodeCtxMay clockSyncNode = do

    let allNodes :: [node]
        allNodes = map (\ (NodeCtxMay nodeP _) -> sing nodeP) allNodeCtxMay

    putStrLn $ "Simulating nodes: " ++ show allNodes

    t0 <- getCurrentTime

    let nodePairs :: [(node, node)]
        nodePairs = [ (nodeFrom, nodeTo)
                    | nodeFrom <- allNodes
                    , nodeTo   <- allNodes
                    , nodeFrom /= nodeTo
                    ]

    netChans :: Map.Map (node, node) (Chan [UpdateList node])
        <- Map.fromList <$> sequence
            [ do
                c  <- newChan
                return ((nodeFrom, nodeTo), c)
            | (nodeFrom, nodeTo) <- nodePairs ]

    localInChans <- Map.fromList <$> sequence [ (node,) <$> newChan
                                              | node <- allNodes ]

    let
        newCtx :: Proxy myNode -> IO (ctxF myNode)
        newCtx = error "TODO"

        actuateNode :: forall (myNode :: node)
                 .  (NodePC myNode)
                 => Maybe (ctxF myNode) -> Proxy myNode -> IO (IO ())
        actuateNode ctxMay myNodeP = do
            ctx <- maybe (newCtx myNodeP) return ctxMay
            actuate
                ctx
                myNodeP
                clockSyncNode
                ((round :: NominalDiffTime -> Integer)
                    .   (* 10^(12::Int))
                    .   flip diffUTCTime t0
                    <$> getCurrentTime)
                circuitM
                (localInChans ! myNode)
                (Map.fromList
                    [ (otherNode,
                        ( netChans ! (myNode, otherNode)
                        , netChans ! (otherNode, myNode)))
                    | otherNode <- allNodes, myNode /= otherNode])
            where
                myNode = sing myNodeP

    let allSomeNodes :: [Some node]
        allSomeNodes = reify allNodes


    -- stopClientA <- actuateNode (Just aCtx) (Proxy @ClientA)
    -- stopClientB <- actuateNode Nothing     (Proxy @ClientB)
    -- stopClientC <- actuateNode Nothing     (Proxy @ClientC)
    -- stopServer  <- actuateNode Nothing     (Proxy @Server)

    -- clickSomeButtons localInChans
    -- mainUI aCtx (localInChans ! ClientA)

    -- putStrLn "Exiting."

    -- stopClientA
    -- stopClientB
    -- stopClientC
    -- stopServer

    return ()