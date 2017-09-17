module Main where

import Control.Concurrent (forkIO)
import Data.IORef
import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Safe
import System.Console.GetOpt
import System.Environment (getArgs)

import qualified Data.Map as M

import Lib
import SumExample

defaultServerPort :: Int
defaultServerPort = 10000

defaultClientPort :: Int
defaultClientPort = 10001

main :: IO ()
main
  -- Args
 = do
  (opts, []) <- argsToOpts =<< getArgs
  runClient (M.fromList [(Client, defaultClientPort), (Server, defaultServerPort)])
  {-
  start $ do
    case optionsMode opts of
      ClientMode srvPort -> do
        let testBeh = mkSumBeh aB bB
        outCtrl <- mkClientGui aB bB
        localActuate testBeh (\o -> set outCtrl [text := o])
      ServerMode -> do
        (aB, aS) <- mkSink Nothing
        (bB, bS) <- mkSink Nothing
        let testBeh = mkSumBeh aB bB
        outCtrl <- mkServerGui aS bS
        localActuate testBeh (\o -> set outCtrl [text := o])

mkServerGui :: Handler (Maybe Int) -> BehaviorSink (Maybe Int) -> IO (StaticText ())
mkServerGui aS bS = mdo
  f <- frame []
  aCtrl <- textEntry f []
  bindSinkMay aS aCtrl
  bCtrl <- textEntry f []
  bindSinkMay bS bCtrl
  outText <- staticText f [text := " "]
  set
    f
    [ layout := minsize (Size 250 400) $ column 0 $
      margin 10 <$>
      [floatCenter (widget aCtrl), floatCenter (widget bCtrl), widget outText]
    ]
  refit f
  return outText

mkClientGui :: Behavior (Maybe Int) -> Behavior (Maybe Int) -> IO (StaticText ())
mkClientGui aS bS = mdo
  f <- frame []
  aCtrl <- staticText f []
  bCtrl <- staticText f []
  outText <- staticText f [text := " "]
  set
    f
    [ layout := minsize (Size 250 400) $ column 0 $
      margin 10 <$>
      [floatCenter (widget aCtrl), floatCenter (widget bCtrl), widget outText]
    ]
  refit f
  return outText

bindSinkMay :: (Read a, Show a) => BehaviorSink (Maybe a) -> TextCtrl () -> IO ()
bindSinkMay sink ctrl = do
  initTextValue <- maybe "" show <$> getSink sink
  set ctrl [text := initTextValue, on update := (setSink sink =<< readMay <$> get ctrl text)]
  return ()
-}

data Options = Options
  { optionsMode :: Mode
  -- , optionsPort :: Int
  }

data Mode
  = ClientMode Int -- ^Port of the server
  | ServerMode
  deriving (Show)

defaultOptions =
  Options
  {optionsMode = ClientMode defaultServerPort, optionsPort = defaultClientPort}

options :: [OptDescr (Options -> Options)]
options =
  [ Option
      ['c']
      ["client"]
      (OptArg
         (\serverPortMay opts ->
            opts
            { optionsMode =
                ClientMode (maybe defaultServerPort read serverPortMay)
            })
         "Server port")
      "ClientMode mode"
  , Option
      ['s']
      ["server"]
      (NoArg (\opts -> opts {optionsMode = ServerMode}))
      "Server mode"
  --, Option
  --    ['p']
  --    ["port"]
  --    (ReqArg (\port opts -> opts {optionsPort = read port}) "port")
  --    "port"
  ]

argsToOpts :: [String] -> IO (Options, [String])
argsToOpts argv =
  case getOpt Permute options argv of
    (o, n, []) -> return (foldl' (flip ($)) defaultOptions o, n)
    (_, _, errs) ->
      ioError (userError (concat errs ++ usageInfo header options))
  where
    header = "Usage: [OPTION...]"
