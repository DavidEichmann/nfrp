{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Module to actuate a circuit description
module Circuit.History
  -- | Data
  ( Transaction(..)
  , encodeTransaction
  , decodeTransaction
  , Diff
  , mkDiff
  , diffTransaction
  , diffCircuit
  , diffAffectedGates
  , diffTime
  , History
  , mkHistory
  , histDiffs
  , histInitialCircuit
  , histCircuit
  , histSplit
  , histApplyTransaction
  ) where

import Circuit.Net ()

import Control.Monad (forM_)
import qualified Data.ByteString as BS
import qualified Data.Map as M
import Data.Serialize
       (Get, Result(..), Serialize(..), runGetPartial, runPut)
import qualified Data.Set as S
import qualified Data.Time as Time
import Safe

import Circuit.Description hiding (sample)

data Transaction = Transaction
  { transactionTime :: Time.UTCTime
  , transactionUpdates :: [GateUpdate]
  }

-- ^ (update, result, changed gates) (most recent is at the head)
data Diff node = Diff
  { diffTransaction :: Transaction
  , diffCircuit :: Circuit node
  , diffAffectedGates :: S.Set GateKey'
  }

mkDiff :: Circuit node -> Transaction -> Diff node
mkDiff c t' = Diff t' c' gate'
  where
    (c', gate'1, gate'2) = applyUpdates c (transactionUpdates t')
    gate' = M.keysSet gate'1 `S.union` M.keysSet gate'2

-- ^ (history deltas (), initial state)
data History node = History
  { histDiffs :: [Diff node] -- ^ Most recent is at the head
  , histInitialCircuit :: Circuit node
  }

mkHistory :: Circuit node -> History node
mkHistory = History []

diffTime :: Diff node -> Time.UTCTime
diffTime = transactionTime . diffTransaction

histCircuit :: History node -> Circuit node
histCircuit hist =
  maybe (histInitialCircuit hist) diffCircuit (headMay (histDiffs hist))

-- TODO support splitting when equal times.... need some way to unambiguously resolve
-- order of transactions!!!
histSplit :: Time.UTCTime -> History node -> ([Diff node], History node)
histSplit time (History diffs initialState) =
  case diffs of
    [] -> ([], History [] initialState)
    currentDiff:prevDiffs ->
      case diffTime currentDiff `compare` time of
        EQ ->
          error
            "need some way to unambiguously resolve order of transactions!!!"
        LT -> ([], History diffs initialState)
        GT ->
          let (splitDeltas', splitHist) =
                histSplit time (History prevDiffs initialState)
          in (currentDiff : splitDeltas', splitHist)

-- | returns new history, old branch of diffs and new branch of diffs.
histApplyTransaction ::
     forall node.
     History node
  -> Transaction
  -> (History node, [Diff node], [Diff node])
histApplyTransaction h t = (h', oldBranch, newBranch)
  where
    h' = History (newBranch ++ histDiffs baseHist) (histInitialCircuit h)
    (oldBranch, baseHist) = histSplit (transactionTime t) h
    oldBranchRevTransactions = diffTransaction <$> reverse oldBranch
    newBranch =
      scanl
        (mkDiff . diffCircuit)
        (mkDiff (histCircuit baseHist) t)
        oldBranchRevTransactions

encodeTransaction :: Transaction -> BS.ByteString
encodeTransaction (Transaction time updates) =
  runPut $ do
    put time
    forM_ updates $ \(GateUpdate key a) -> do
      put (gateKeyToInt key)
      put a

decodeTransaction :: Circuit node -> BS.ByteString -> Either String Transaction
decodeTransaction circuit fullStr = do
  (time, updatesStr) <- runGetPartial' (get @Time.UTCTime) fullStr
  updates <- decodeGateUpdates updatesStr
  return (Transaction time updates)
  where
    gateKeys = circuitGateKeysByInt circuit
    decodeGateUpdates :: BS.ByteString -> Either String [GateUpdate]
    decodeGateUpdates str
      | BS.null str = Right []
      | otherwise
        -- Parse gate index
       = do
        (gateInt, str') <- runGetPartial' (get @Int) str
        -- Infer the type, a, by looking up the GateKey' from gateKeys.
        case M.lookup gateInt gateKeys of
          Just (GateKey' (gateKey :: GateKey gateType a)) -> do
            (a, str'') <- runGetPartial' (get :: Get a) str'
            otherUpdates <- decodeGateUpdates str''
            return (GateUpdate gateKey a : otherUpdates)
          Nothing ->
            error $
            "Could not find gate " ++
            show gateInt ++ " in : " ++ show (M.keys gateKeys)
    runGetPartial' getter str =
      case runGetPartial getter str of
        Fail err _ -> Left $ "Failed to parse a transaction: " ++ err
        Partial _ -> Left "Only managed to partially parse a transaction."
        Done time remainingStr -> Right (time, remainingStr)
