{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module SumExample where

import Control.Monad
import Data.IORef
import Data.Kind
import qualified Data.Map as M
import Data.Proxy
import qualified Graphics.UI.Gtk as Gtk

import Circuit.Actuate

data Node
  = Server
  | Client

newtype ServerInputs = ServerInputs
  { serverIntAddHandler :: E Int
  }

newtype ClientInputs = ClientInputs
  { clientIntAddHandler :: E Int
  }

data SumOuts = SumOuts
  { serverIntB :: B Int
  , clientIntB :: B Int
  , sumB :: B Int
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
      , SumOuts {serverIntB = serverIntB, clientIntB = clientIntB, sumB = sumB})

runClient :: M.Map Node Int -> IO ()
runClient nodeAddresses
  -- Initialize Gtk.
 = do
  _args <- Gtk.initGUI
  -- Create the window.
  window <- Gtk.windowNew
  Gtk.containerSetBorderWidth window 10
  Gtk.windowSetDefaultSize window 300 300
  Gtk.onDelete
    window
    (\_ -> do
       Gtk.mainQuit
       return False)
  -- Create the text entry.
  entry <- Gtk.entryNew
  Gtk.entrySetText entry "Hello World!"
  Gtk.containerAdd window entry
  Gtk.widgetShow entry
  -- Create text widget
  serverTextView <- Gtk.textViewNew
  Gtk.containerAdd window serverTextView
  Gtk.widgetShow serverTextView
  -- Display window
  Gtk.widgetShow window
  -- Actuate the FRP circuit
  circuit <- actuate sumCircuit Client
  -- Start main loop.
  Gtk.mainGUI
