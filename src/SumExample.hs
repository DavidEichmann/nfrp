{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module SumExample where

import Control.Monad.Trans.Class (lift)
import Control.Exception (finally)
import qualified Data.Map as M
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Graphics.UI.Gtk (AttrOp(..))
import qualified Graphics.UI.Gtk as Gtk
import Safe (readDef)

import Lib

data Node
  = Server
  | Client
  deriving (Generic, Serialize, Show, Eq, Ord)








sumCircuit :: Circuit Node
serverIntESinkKey :: E Int
clientIntESinkKey :: E Int
serverIntBKey :: B Int
clientIntBKey :: B Int
sumBKey :: B Int
((serverIntESinkKey, clientIntESinkKey, serverIntBKey, clientIntBKey, sumBKey), sumCircuit) =
  mkCircuit $
   do
    -- Input Int change events for client and for server.
    serverIntESink <- localE Server
    clientIntESink <- localE Client
    -- Convert to behaviors (initially set to 0).
    serverIntB <- stepper 0 serverIntESink
    clientIntB <- stepper 0 clientIntESink
    -- Sum the server and client ints.
    sumB <- liftB2 (+) serverIntB clientIntB
    -- return events and behaviors.
    return
      ( serverIntESink
      , clientIntESink
      , serverIntB
      , clientIntB
      , sumB)









run :: M.Map Node Int -> Node -> IO ()
run nodeAddresses ownerNode
  -- Initialize Gtk.
 = do
  let (ownerIntEKey, ownerIntBKey, remoteIntBKey) =
        case ownerNode of
          Server -> (serverIntESinkKey, serverIntBKey, clientIntBKey)
          Client -> (clientIntESinkKey, clientIntBKey, serverIntBKey)
  _args <- Gtk.initGUI
  -- Create the window.
  window <- Gtk.windowNew
  Gtk.set window [Gtk.windowTitle := show ownerNode]
  Gtk.containerSetBorderWidth window 10
  Gtk.windowSetDefaultSize window 300 300
  _ <-
    Gtk.on
      window
      Gtk.destroyEvent
      (do
         lift Gtk.mainQuit
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
  -- Actuate the FRP circuit
  (performTransaction, closeSockets) <-
    actuate
      nodeAddresses
      ownerNode
      sumCircuit
      [ Listener remoteIntBKey (Gtk.labelSetText remoteIntLabel . show)
      , Listener sumBKey (Gtk.labelSetText sumIntLabel . show)
      -- , Listener ownerIntBKey (\ownerInt -> putStrLn $ "OwnerInt: " ++ show ownerInt)
      -- , Listener remoteIntBKey (\remoteInt -> putStrLn $ "RemoteInt: " ++ show remoteInt)
      -- , Listener (soSumB sumOuts) (\sumInt -> putStrLn $ "SumInt: " ++ show sumInt)
      ]
  -- Transaction hooks.
  entryBuffer <- Gtk.entryGetBuffer entry
  _ <-
    Gtk.on
      entryBuffer
      (Gtk.entryBufferInsertedText @Gtk.EntryBuffer @String)
      (\_ _ _ -> do
        -- perform transaction.
        localInt <- readDef 0 <$> Gtk.entryGetText entry
        performTransaction [GateUpdate ownerIntEKey localInt])
  -- Start main loop.
  Gtk.mainGUI `finally` closeSockets
