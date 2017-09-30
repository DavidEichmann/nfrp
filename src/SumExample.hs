{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module SumExample where

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

newtype ServerInputs = ServerInputs
  { serverIntAddHandler :: E Int
  }

newtype ClientInputs = ClientInputs
  { clientIntAddHandler :: E Int
  }

data SumOuts = SumOuts
  { soServerIntB :: B Int
  , soClientIntB :: B Int
  , soSumB :: B Int
  }

clientInputs :: ClientInputs
serverInputs :: ServerInputs
sumOuts :: SumOuts
sumCircuit :: Circuit Node
((clientInputs, serverInputs, sumOuts), sumCircuit) =
  mkCircuit $
    -- Define inputs
   do
    clientInt <- localE Client
    serverInt <- localE Server
    serverIntB <- stepper 0 serverInt
    clientIntB <- stepper 0 clientInt
    sumB <- liftB2 (+) serverIntB clientIntB
    -- return observations
    return
      ( ClientInputs clientInt
      , ServerInputs serverInt
      , SumOuts
        {soServerIntB = serverIntB, soClientIntB = clientIntB, soSumB = sumB})

run :: M.Map Node Int -> Node -> IO ()
run nodeAddresses ownerNode
  -- Initialize Gtk.
 = do
  let (ownerIntB, remoteIntB) =
        case ownerNode of
          Server -> (soServerIntB sumOuts, soClientIntB sumOuts)
          Client -> (soClientIntB sumOuts, soServerIntB sumOuts)
  _args <- Gtk.initGUI
  -- Create the window.
  window <- Gtk.windowNew
  Gtk.set window [Gtk.windowTitle := show ownerNode]
  Gtk.containerSetBorderWidth window 10
  Gtk.windowSetDefaultSize window 300 300
  --_onDeleteWindowConnectId <-
  --  Gtk.onDestroy
  --    window
  --    (\_ -> do
  --       Gtk.mainQuit
  --       return False)
  -- Vertical layout.
  box <- Gtk.vBoxNew True 0
  -- Create label
  remoteIntLabel <- Gtk.labelNew @String Nothing
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
      [ Listener remoteIntB (Gtk.labelSetText remoteIntLabel . show)
      , Listener (soSumB sumOuts) (Gtk.labelSetText sumIntLabel . show)
      ]
  -- Transaction hooks.
  entryBuffer <- Gtk.entryGetBuffer entry
  _ <-
    Gtk.on
      entryBuffer
      (Gtk.entryBufferInsertedText @Gtk.EntryBuffer @String)
      (\_ _ _ -> do
         putStrLn "-"
         text <- readDef 0 <$> Gtk.entryGetText entry
         performTransaction (Transaction 0 [GateUpdate ownerIntB text]))
  -- Start main loop.
  Gtk.mainGUI `finally` closeSockets
