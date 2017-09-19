{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module SumExample where

import qualified Data.Map as M
import qualified Graphics.UI.Gtk as Gtk

import Lib

data Node
  = Server
  | Client
  deriving (Show, Eq, Ord)

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

runClient :: M.Map Node Int -> IO ()
runClient nodeAddresses
  -- Initialize Gtk.
 = do
  _args <- Gtk.initGUI
  -- Create the window.
  window <- Gtk.windowNew
  Gtk.containerSetBorderWidth window 10
  Gtk.windowSetDefaultSize window 300 300
  _onDeleteWindowConnectId <-
    Gtk.onDelete
      window
      (\_ -> do
         Gtk.mainQuit
         return False)
  -- Vertical layout.
  box <- Gtk.vBoxNew True 0
  -- Create the text entry.
  entry <- Gtk.entryNew
  Gtk.entrySetText entry "Hello World!"
  Gtk.boxPackEnd box entry Gtk.PackGrow 0
  -- Create text widget
  serverTextView <- Gtk.textViewNew
  Gtk.boxPackEnd box serverTextView Gtk.PackGrow 0
  -- Display window
  Gtk.containerAdd window box
  Gtk.widgetShow box
  Gtk.widgetShow window
  -- Actuate the FRP circuit
  circuit <- actuate nodeAddresses Client sumCircuit
  --subscribeB
  --  circuit
  --  (soServerIntB sumOuts)
  --  (\serverInt -> do
  --     textBuffer <- Gtk.textViewGetBuffer serverTextView
  --     Gtk.textBufferSetText textBuffer (show serverInt))
  -- Start main loop.
  Gtk.mainGUI
