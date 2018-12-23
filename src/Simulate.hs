{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
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

import Data.Typeable
import Data.Map ((!))
import qualified Data.Map as Map
import NFRP

import Data.Kind
import Control.Monad (forM)
import Data.Time.Clock (NominalDiffTime, getCurrentTime, diffUTCTime)
import Control.Concurrent (Chan, newChan)

data NodeCtx node (ctxF :: node -> Type)
  = forall (myNode :: node) . NodePC myNode => NodeCtx (Proxy myNode) (ctxF myNode)

simulate :: forall (node :: Type) (ctxF :: node -> Type)
         .  (NodeC node)
         => Moment node ctxF ()   -- ^ Ciruit to simulate
         -> [NodeCtx node ctxF]   -- ^ Nodes  to simulate
         -> node                  -- ^ clockSyncNode
         -> IO (IO ())            -- ^ returns an IO action that stops the simulation.
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

    netChans :: Map.Map (node, node) (Chan [UpdateList node])
        <- Map.fromList <$> sequence
            [ do
                c  <- newChan
                return ((nodeFrom, nodeTo), c)
            | (nodeFrom, nodeTo) <- nodePairs ]

    localInChans <- Map.fromList <$> sequence [ (node,) <$> newChan
                                              | node <- allNodes ]

    let actuateNode :: forall (myNode :: node)
                 .  (NodePC myNode)
                 => ctxF myNode -> Proxy myNode -> IO (IO ())
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
                (localInChans ! myNode)
                (Map.fromList
                    [ (otherNode,
                        ( netChans ! (myNode, otherNode)
                        , netChans ! (otherNode, myNode)))
                    | otherNode <- allNodes, myNode /= otherNode])
            where
                myNode = sing myNodeP

    stops <- forM allNodeCtxMay $ \ (NodeCtx nodeP ctx) ->
        actuateNode ctx nodeP

    return $ sequence_ stops