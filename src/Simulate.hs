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

module Simulate where

import Data.Kind
import Data.Map (Map, fromList, (!), empty, insert)
import NFRP

import Control.Monad (foldM)
import Data.Time.Clock (NominalDiffTime, getCurrentTime, diffUTCTime)
import Control.Concurrent (Chan, newChan)

data NodeCtx mt where
  NodeCtx :: MomentNode mt
          -> MomentCtx mt
          -> NodeCtx mt

simulate :: forall node (ctx :: Type) mkCircuitOut
         .  NodeC node
         => Moment (MomentTypes node ctx) mkCircuitOut   -- ^ Ciruit to simulate
         -> [NodeCtx (MomentTypes node ctx)]             -- ^ Nodes  to simulate
         -> node          -- ^ clockSyncNode
         -> IO ( IO ()               -- ^ (returns an IO action that stops the simulation.
               , Map node mkCircuitOut
               , Map node (EventInjector node)  -- ^ output from building the circuits per node.
               , Map node (IO Time))              -- ^ adjusted clocks
simulate circuitM allNodeCtxMay clockSyncNode = do

    let allNodes :: [node]
        allNodes = map (\ (NodeCtx node _) -> node) allNodeCtxMay

    t0 <- getCurrentTime

    let nodePairs :: [(node, node)]
        nodePairs = [ (nodeFrom, nodeTo)
                    | nodeFrom <- allNodes
                    , nodeTo   <- allNodes
                    , nodeFrom /= nodeTo
                    ]

    netChans :: Map (node, node) (Chan [UpdateList])
        <- fromList <$> sequence
            [ do
                c  <- newChan
                return ((nodeFrom, nodeTo), c)
            | (nodeFrom, nodeTo) <- nodePairs ]

    let actuateNode
            :: ctx
            -> node
            -> IO ( IO ()
                , mkCircuitOut
                , EventInjector node
                , IO Time)
        actuateNode ctx myNode
            = actuate
                ctx
                myNode
                clockSyncNode
                ((round :: NominalDiffTime -> Integer)
                    .   (* 10^(12::Int))
                    .   flip diffUTCTime t0
                    <$> getCurrentTime)
                circuitM
                (fromList
                    [ (otherNode,
                        ( netChans ! (myNode, otherNode)
                        , netChans ! (otherNode, myNode)))
                    | otherNode <- allNodes, myNode /= otherNode])

    foldM
        (\ (stopAcc, outsAcc, injectorsAcc, clocksAcc) (NodeCtx node ctx) -> do
            (stopI, outI, injectorI, clockI) <- actuateNode ctx node
            return ( stopAcc >> stopI
                   , insert    node  outI      outsAcc
                   , insert    node  injectorI injectorsAcc
                   , insert    node  clockI    clocksAcc
                   )
        )
        (return(), empty, empty, empty)
        allNodeCtxMay