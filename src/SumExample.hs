{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module SumExample where

import Control.Concurrent.Async
import qualified Control.Concurrent.MVar as MV
import Control.Exception (bracket)
import Control.Monad.Trans.Class (lift)
import qualified Data.Map as M
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Graphics.UI.Gtk (AttrOp(..))
import qualified Graphics.UI.Gtk as Gtk
import qualified Network.Socket as Net
import Safe (readDef)

import Lib

-- |The network consists of two nodes.
data Node
  = NodeA
  | NodeB
  deriving (Generic, Serialize, Show, Read, Eq, Ord, Bounded, Enum)

-- |NFRP circuit takes an Int from each node and sums them.
sumCircuit :: Circuit Node
-- |Event sink for changes to nodeA's Int.
nodeAIntESink :: E Int
-- |Event sink for changes to nodeB's Int.
nodeBIntESink :: E Int
-- |Behavior of node A's Int.
nodeAIntB :: B Int
-- |Behavior of node B's Int.
nodeBIntB :: B Int
-- |Behavior of the sum of both nodes' Ints.
sumB :: B Int
((nodeAIntESink, nodeBIntESink, nodeAIntB, nodeBIntB, sumB), sumCircuit) =
  mkCircuit $
    -- |Event sourced from NodeA
   do
    nodeAIntESink' <- localE NodeA
     -- |Event sourced from NodeB
    nodeBIntESink' <- localE NodeB
    -- Convert to behaviors (initially set to 0).
    nodeAIntB' <- stepper 0 nodeAIntESink'
    nodeBIntB' <- stepper 0 nodeBIntESink'
    -- Sum the nodeA and nodeB ints.
    sumB' <- liftB2 (+) nodeAIntB' nodeBIntB'
    -- return events and behaviors.
    return (nodeAIntESink', nodeBIntESink', nodeAIntB', nodeBIntB', sumB')

run :: M.Map Node (Net.HostName, Int) -> Node -> IO (Async ())
run hostNames ownerNode
  -- Initialize Gtk.
 =
  async $
  -- Use MVar to wait for window close.
   do
    exitMVar <- MV.newEmptyMVar
    let (ownerIntE, _ownerIntB, remoteIntB) =
          case ownerNode of
            NodeA -> (nodeAIntESink, nodeAIntB, nodeBIntB)
            NodeB -> (nodeBIntESink, nodeBIntB, nodeAIntB)
    (remoteIntLabel, sumIntLabel, entry) <-
      Gtk.postGUISync $
    -- Create the window.
       do
        window <- Gtk.windowNew
        Gtk.set window [Gtk.windowTitle := show ownerNode]
        Gtk.containerSetBorderWidth window 10
        Gtk.windowSetDefaultSize window 300 300
        _ <-
          Gtk.on
            window
            Gtk.destroyEvent
            (do lift Gtk.mainQuit
                return False)
    -- Vertical layout.
        box <- Gtk.vBoxNew True 0
    -- Create label
        remoteIntLabel <- Gtk.labelNew (Just "remote value")
        Gtk.boxPackStart box remoteIntLabel Gtk.PackGrow 0
        Gtk.widgetShow remoteIntLabel
    -- Create the text entry.
        entry <- Gtk.entryNew
        Gtk.entrySetText entry ""
        Gtk.boxPackStart box entry Gtk.PackGrow 0
        Gtk.widgetShow entry
    -- Create sum label
        sumIntLabel <- Gtk.labelNew (Just "sum")
        Gtk.boxPackStart box sumIntLabel Gtk.PackGrow 0
        Gtk.widgetShow sumIntLabel
    -- Display window
        Gtk.containerAdd window box
        Gtk.widgetShow box
        Gtk.widgetShow window
        _ <-
          Gtk.on
            window
            Gtk.destroyEvent
            (do lift $ MV.putMVar exitMVar ()
                return True)
        return (remoteIntLabel, sumIntLabel, entry)
  -- Actuate the FRP circuit
    bracket
      (actuate
         hostNames
         ownerNode
         sumCircuit
         [ Setter
             remoteIntB
             (Gtk.postGUISync . Gtk.labelSetText remoteIntLabel . show)
         , Setter sumB (Gtk.postGUISync . Gtk.labelSetText sumIntLabel . show)
      -- , Setter ownerIntB (\ownerInt -> putStrLn $ "OwnerInt: " ++ show ownerInt)
      -- , Setter remoteIntB (\remoteInt -> putStrLn $ "RemoteInt: " ++ show remoteInt)
      -- , Setter (soSumB sumOuts) (\sumInt -> putStrLn $ "SumInt: " ++ show sumInt)
         ])
      (\(_, closeSockets) -> closeSockets)
      (\(performTransaction, _) -> do
         Gtk.postGUISync $
        -- Transaction hooks.
          do
           entryBuffer <- Gtk.entryGetBuffer entry
           _ <-
             Gtk.on
               entryBuffer
               (Gtk.entryBufferInsertedText @Gtk.EntryBuffer @String)
               (\_ _ _
              -- perform transaction.
                 -> do
                  localInt <- readDef 0 <$> Gtk.entryGetText entry
                  performTransaction [GateUpdate ownerIntE localInt])
           return ()
      -- Return wait for close.
         MV.takeMVar exitMVar)
