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

import Data.Typeable
import Data.Map (Map, fromList, (!), empty, insert)
import NFRP
import qualified HMap as HM

import Control.Monad (foldM)
import Data.Time.Clock (NominalDiffTime, getCurrentTime, diffUTCTime)
import Control.Concurrent (Chan, newChan)

data NodeCtx mt where
  NodeCtx :: forall mt (myNode :: MomentNode mt)
          .  NodePC myNode
          => Proxy mt
          -> Proxy (myNode :: MomentNode mt)
          -> MomentCtx mt
          -> NodeCtx mt

simulate :: forall mt mkCircuitOut
         .  NodeC (MomentNode mt)
         => Moment mt mkCircuitOut   -- ^ Ciruit to simulate
         -> [NodeCtx mt]             -- ^ Nodes  to simulate
         -> (MomentNode mt)          -- ^ clockSyncNode
         -> IO ( IO ()               -- ^ (returns an IO action that stops the simulation.
               , Map (MomentNode mt) mkCircuitOut
               , HM.HMap (MomentNode mt) EventInjector       -- ^ output from building the circuits per (MomentNode mt).
               , Map (MomentNode mt) (IO Time))              -- ^ adjusted clocks
simulate circuitM allNodeCtxMay clockSyncNode = do

    let allNodes :: [MomentNode mt]
        allNodes = map (\ (NodeCtx _ nodeP _) -> sing nodeP) allNodeCtxMay

    t0 <- getCurrentTime

    let nodePairs :: [(MomentNode mt, MomentNode mt)]
        nodePairs = [ (nodeFrom, nodeTo)
                    | nodeFrom <- allNodes
                    , nodeTo   <- allNodes
                    , nodeFrom /= nodeTo
                    ]

    netChans :: Map (MomentNode mt, MomentNode mt) (Chan [UpdateList (MomentNode mt)])
        <- fromList <$> sequence
            [ do
                c  <- newChan
                return ((nodeFrom, nodeTo), c)
            | (nodeFrom, nodeTo) <- nodePairs ]

    let actuateNode :: forall (myNode :: MomentNode mt)
                 .  (NodePC myNode)
                 => MomentCtx mt
                 -> Proxy myNode
                 -> IO ( IO ()
                       , mkCircuitOut
                       , EventInjector myNode
                       , IO Time)
        actuateNode ctx myNodeP
            = actuate
                ctx
                myNodeP
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
            where
                myNode = sing myNodeP

    foldM
        (\ (stopAcc, outsAcc, injectorsAcc, clocksAcc) (NodeCtx _ nodeP ctx) -> do
            (stopI, outI, injectorI, clockI) <- actuateNode ctx nodeP
            let node = sing nodeP
            return ( stopAcc >> stopI
                   , insert    node  outI      outsAcc
                   , HM.insert nodeP injectorI injectorsAcc
                   , insert    node  clockI    clocksAcc
                   )
        )
        (return(), empty, HM.empty, empty)
        allNodeCtxMay