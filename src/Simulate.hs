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

import Data.Kind
import Control.Monad (foldM)
import Data.Time.Clock (NominalDiffTime, getCurrentTime, diffUTCTime)
import Control.Concurrent (Chan, newChan)

data NodeCtx node (ctxF :: node -> Type)
  = forall (myNode :: node)
  . NodePC myNode
  => NodeCtx (Proxy myNode) (ctxF myNode)

simulate :: forall (node :: Type) (ctxF :: node -> Type) mkCircuitOut
         .  (NodeC node)
         => Moment node ctxF mkCircuitOut   -- ^ Ciruit to simulate
         -> [NodeCtx node ctxF]   -- ^ Nodes  to simulate
         -> node                  -- ^ clockSyncNode
         -> IO ( IO ()            -- ^ (returns an IO action that stops the simulation.
               , Map node mkCircuitOut
               , HM.HMap node EventInjector       -- ^ output from building the circuits per node.
               )
simulate circuitM allNodeCtxMay clockSyncNode = do

    let allNodes :: [node]
        allNodes = map (\ (NodeCtx nodeP _) -> sing nodeP) allNodeCtxMay

    t0 <- getCurrentTime

    let nodePairs :: [(node, node)]
        nodePairs = [ (nodeFrom, nodeTo)
                    | nodeFrom <- allNodes
                    , nodeTo   <- allNodes
                    , nodeFrom /= nodeTo
                    ]

    netChans :: Map (node, node) (Chan [UpdateList node])
        <- fromList <$> sequence
            [ do
                c  <- newChan
                return ((nodeFrom, nodeTo), c)
            | (nodeFrom, nodeTo) <- nodePairs ]

    let actuateNode :: forall (myNode :: node)
                 .  (NodePC myNode)
                 => ctxF myNode
                 -> Proxy myNode
                 -> IO ( IO ()
                       , mkCircuitOut
                       , EventInjector myNode
                       )
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
        (\ (stopAcc, outsAcc, injectorsAcc) (NodeCtx nodeP ctx) -> do
            (stopI, outI, injectorI) <- actuateNode ctx nodeP
            return ( stopAcc >> stopI
                   , insert    (sing nodeP) outI      outsAcc
                   , HM.insert nodeP        injectorI injectorsAcc
                   )
        )
        (return(), empty, HM.empty)
        allNodeCtxMay