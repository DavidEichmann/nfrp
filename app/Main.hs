module Main where

import Data.IORef
import Data.List (foldl')
import Lib
import System.Console.GetOpt
import System.Environment (getArgs)

compilerOpts :: [String] -> IO (Options, [String])
compilerOpts argv =
  case getOpt Permute options argv of
    (o, n, []) -> return (foldl' (flip ($)) defaultOptions o, n)
    (_, _, errs) ->
      ioError (userError (concat errs ++ usageInfo header options))
  where
    header = "Usage: [OPTION...]"

main :: IO ()
main
  -- Args
 = do
  (opts, []) <- compilerOpts =<< getArgs
  -- FRP Behavior
  inputA <- newIORef 10
  inputB <- newIORef 20
  let aBeh :: Behavior Int
      aBeh = Poll (readIORef inputA)
      bBeh :: Behavior Int
      bBeh = Poll (readIORef inputB)
      testBeh :: Behavior String
      testBeh =
        Lift2
          (\a b -> show a ++ " + " ++ show b ++ " = " ++ show (a + b))
          aBeh
          bBeh
  -- Actuate
  localActuate
    testBeh
    (\out -> do
       modifyIORef inputA (+ 1)
       putStrLn out)
  --case optionsMode opts of
  --  Client srvPort -> netActuateClient srvPort clientBehavior
  --  Server -> netActuateServer clientBehavior

data Options = Options
  { optionsMode :: Mode
  , optionsPort :: Int
  }

data Mode
  = Client Int -- ^Port of the server
  | Server
  deriving (Show)

defaultServerPort = 10000

defaultClientPort = 10001

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
