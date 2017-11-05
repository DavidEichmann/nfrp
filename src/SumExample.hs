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

data Node
  = Server
  | Client
  deriving (Generic, Serialize, Show, Read, Eq, Ord, Bounded, Enum)

sumCircuit :: Circuit Node
serverIntESinkKey :: E Int
clientIntESinkKey :: E Int
serverIntBKey :: B Int
clientIntBKey :: B Int
sumBKey :: B Int
((serverIntESinkKey, clientIntESinkKey, serverIntBKey, clientIntBKey, sumBKey), sumCircuit) =
  mkCircuit $
    -- Input Int change events for client and for server.
   do
    serverIntESink <- localE Server
    clientIntESink <- localE Client
    -- Convert to behaviors (initially set to 0).
    serverIntB <- stepper 0 serverIntESink
    clientIntB <- stepper 0 clientIntESink
    -- Sum the server and client ints.
    sumB <- liftB2 (+) serverIntB clientIntB
    -- return events and behaviors.
    return (serverIntESink, clientIntESink, serverIntB, clientIntB, sumB)

run :: M.Map Node (Net.HostName, Int) -> Node -> IO (Async ())
run hostNames ownerNode
  -- Initialize Gtk.
 =
  async $
  -- Use MVar to wait for window close.
   do
    exitMVar <- MV.newEmptyMVar
    let (ownerIntEKey, _ownerIntBKey, remoteIntBKey) =
          case ownerNode of
            Server -> (serverIntESinkKey, serverIntBKey, clientIntBKey)
            Client -> (clientIntESinkKey, clientIntBKey, serverIntBKey)
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
             remoteIntBKey
             (Gtk.postGUISync . Gtk.labelSetText remoteIntLabel . show)
         , Setter
             sumBKey
             (Gtk.postGUISync . Gtk.labelSetText sumIntLabel . show)
      -- , Setter ownerIntBKey (\ownerInt -> putStrLn $ "OwnerInt: " ++ show ownerInt)
      -- , Setter remoteIntBKey (\remoteInt -> putStrLn $ "RemoteInt: " ++ show remoteInt)
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
                  performTransaction [GateUpdate ownerIntEKey localInt])
           return ()
      -- Return wait for close.
         MV.takeMVar exitMVar)
