module Main where

import qualified Network.Socket as Net
import Data.List (foldl')
import System.Console.GetOpt
import System.Environment (getArgs)

import qualified Data.Map as M

import SumExample

defaultNodeAddresses :: M.Map Node Net.SockAddr
defaultNodeAddresses = M.fromList (zip
  [minBound..maxBound]
  [Net.SockAddrInet port (Net.tupleToHostAddress (127, 0, 0, 1)) | port <- [10000..]])

main :: IO ()
main
  -- Args
 = do
  remoteHostName : args <- getArgs
  (Options mode, []) <- argsToOpts args
  let (remote, owner)
        = case mode of
          ClientMode -> (Server, Client)
          ServerMode -> (Client, Server)
  let Net.SockAddrInet remotePort _ = defaultNodeAddresses M.! remote
  remoteAddrInfo : _ <- Net.getAddrInfo
    Nothing
    (Just remoteHostName)
    (Just (show remotePort))
  let nodeAddresses
        = M.insert remote (Net.addrAddress remoteAddrInfo) defaultNodeAddresses
  print nodeAddresses
  run nodeAddresses owner

data Options = Options
  { optionsMode :: Mode
  }

data Mode
  = ClientMode
  | ServerMode
  deriving (Show)

defaultOptions :: Options
defaultOptions = Options {optionsMode = ClientMode}

options :: [OptDescr (Options -> Options)]
options =
  [ Option
      ['c']
      ["client"]
      (NoArg (\opts -> opts {optionsMode = ClientMode}))
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
