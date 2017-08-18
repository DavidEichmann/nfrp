{-# LANGUAGE RecursiveDo #-}

module Main where

import Control.Concurrent (forkIO)
import Data.IORef
import Data.List (foldl')
import Graphics.UI.WX
import Lib
import Safe
import System.Console.GetOpt
import System.Environment (getArgs)

defaultServerPort :: Int
defaultServerPort = 10000

defaultClientPort :: Int
defaultClientPort = 10001

main :: IO ()
main
  -- Args
 = do
  (opts, []) <- argsToOpts =<< getArgs
  -- FRP Behavior
  (aB, aS) <- mkSink Nothing
  (bB, bS) <- mkSink Nothing
  let testBeh :: Behavior String
      testBeh =
        Lift2 (\a b -> show a ++ " + " ++ show b ++ " = " ++ show ((+) <$> a <*> b)) aB bB
  start $ do
    -- Actuate
    outCtrl <- mkGui aS bS
    localActuate testBeh (\o -> set outCtrl [text := o])
    --case optionsMode opts of
    --  Client srvPort -> netActuateClient srvPort clientBehavior
    --  Server -> netActuateServer clientBehavior

mkGui :: BehaviorSink (Maybe Int) -> BehaviorSink (Maybe Int) -> IO (StaticText ())
mkGui aS bS = mdo
  a <- maybe "" show <$> getSink aS
  b <- maybe "" show <$> getSink bS
  f <- frame []
  aCtrl <-
    textEntry
      f
      [text := a, on update := (setSink aS =<< readMay <$> get aCtrl text)]
  bCtrl <-
    textEntry
      f
      [text := b, on update := (setSink bS =<< readMay <$> get bCtrl text)]
  outText <- staticText f [text := " "]
  set
    f
    [ layout := column 0 $
      margin 10 <$>
      [floatCenter (widget aCtrl), floatCenter (widget bCtrl), widget outText]
    ]
  refit f
  return outText

data Options = Options
  { optionsMode :: Mode
  , optionsPort :: Int
  }

data Mode
  = Client Int -- ^Port of the server
  | Server
  deriving (Show)

defaultOptions =
  Options
  {optionsMode = Client defaultServerPort, optionsPort = defaultClientPort}

options :: [OptDescr (Options -> Options)]
options =
  [ Option
      ['c']
      ["client"]
      (OptArg
         (\serverPortMay opts ->
            opts
            {optionsMode = Client (maybe defaultServerPort read serverPortMay)})
         "Server port")
      "Client mode"
  , Option
      ['s']
      ["server"]
      (NoArg (\opts -> opts {optionsMode = Server}))
      "Server mode"
  , Option
      ['p']
      ["port"]
      (ReqArg (\port opts -> opts {optionsPort = read port}) "port")
      "port"
  ]

argsToOpts :: [String] -> IO (Options, [String])
argsToOpts argv =
  case getOpt Permute options argv of
    (o, n, []) -> return (foldl' (flip ($)) defaultOptions o, n)
    (_, _, errs) ->
      ioError (userError (concat errs ++ usageInfo header options))
  where
    header = "Usage: [OPTION...]"
