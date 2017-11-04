module Main where

import Data.List (foldl')
import Control.Concurrent.Async
import Control.Concurrent
import System.Console.GetOpt
import System.Environment (getArgs)
import qualified Graphics.UI.Gtk as Gtk

import qualified Data.Map as M
import qualified Data.Set as S

import Circuit.Actuate (baseNfrpPort)
import SumExample

extract :: [String] -> [(Node, String)]
extract [] = []
extract [_] = error "args must be in the form: (Node hostname)*"
extract (node:hostName:rest) = (read node, hostName) : extract rest

allNodes :: [Node]
allNodes = [minBound .. maxBound]

allNodesSet :: S.Set Node
allNodesSet = S.fromList allNodes

defaultHostNameAndPorts :: M.Map Node (String, Int)
defaultHostNameAndPorts =
  M.fromList (zip allNodes (zip (repeat "localhost") [baseNfrpPort ..]))

-- expect list of "node hostname" for all external nodes
main :: IO ()
main
  -- Args
 = do
  remotes <- extract <$> getArgs
  let localNodes = allNodesSet `S.difference` (S.fromList . map fst $ remotes)
      hostNameAndPorts =
        M.mergeWithKey
          (\_ (_, port) hostName -> Just (hostName, port))
          id
          (const M.empty)
          defaultHostNameAndPorts
          (M.fromList remotes)
  putStrLn $ "localNodes: " ++ show localNodes

  -- Initialize Gtk+ and start main loop in hackground thread.
  _args <- Gtk.initGUI
  _ <- forkIO Gtk.mainGUI

  runningAsyncClients <- mapM (run hostNameAndPorts) (S.toList localNodes)
  mapM_ wait . reverse $ runningAsyncClients

  -- End GUI
  Gtk.mainQuit

data Options = Options
  { optionsMode :: [Node]
  }

defaultOptions :: Options
defaultOptions = Options {optionsMode = [minBound .. maxBound]}

options :: [OptDescr (Options -> Options)]
options =
  [ Option
      ['c']
      ["client"]
      (NoArg (\opts -> opts {optionsMode = [Client]}))
      "ClientMode mode"
  , Option
      ['s']
      ["server"]
      (NoArg (\opts -> opts {optionsMode = [Server]}))
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
