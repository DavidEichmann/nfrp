module Main where

import Data.List (foldl')
import System.Concurrent.Async
import System.Console.GetOpt
import System.Environment (getArgs)

import qualified Data.Map as M
import qualified Data.Set as S

import Circuit.Actuate (nfrpPort)
import SumExample

extract :: [String] -> [(Node, String)]
extract (node:hostName:rest) = (read node, hostName) : extract rest
extract [] = []

allNodes :: [Node]
allNodes = [minBound .. maxBound]

allNodesSet :: S.Set Node
allNodesSet = S.fromList allNodes

defaultHostNameAndPorts :: M.Map Node (String, Int)
defaultHostNameAndPorts =
  M.fromList (zip allNodes (zip (repeat "localhost") [nfrpPort ..]))

-- expect list of "node hostname" for all external nodes
main :: IO ()
main
  -- Args
 = do
  remotes <- extract <$> getArgs
  let localNodes = allNodesSet S.difference (S.fromList . map fst $ remotes)
      hostNameAndPorts =
        M.mergeWithKey
          (\_ (_, port) hostName -> (hostName, port))
          id
          (const M.empty)
          defaultHostNameAndPorts
          (M.fromList remotes)
  putStrLn $ "localNodes: " ++ show nodeHostNames
  runningAsyncClients <- mapM (async . run hostNameAndPorts) localNodes
  mapM_ wait runningAsyncClients

data Options = Options
  { optionsMode :: [Node]
  }

defaultOptions :: Options
defaultOptions = Options {optionsMode = [minBound .. maxBound]}

options :: [OptDescr (Options -> Options)]
options =
  [ Option
      ['a']
      ["all"]
      (NoArg (\opts -> opts {optionsMode = [minBound .. maxBound]}))
      Option
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
