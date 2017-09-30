module Main where

import Data.List (foldl')
import System.Console.GetOpt
import System.Environment (getArgs)

import qualified Data.Map as M

import SumExample

defaultServerPort :: Int
defaultServerPort = 10000

defaultClientPort :: Int
defaultClientPort = 10001

nodeAddresses :: M.Map Node Int
nodeAddresses =
  M.fromList [(Client, defaultClientPort), (Server, defaultServerPort)]

main :: IO ()
main
  -- Args
 = do
  (Options mode, []) <- argsToOpts =<< getArgs
  case mode of
    ClientMode -> run nodeAddresses Client
    ServerMode -> run nodeAddresses Server

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
