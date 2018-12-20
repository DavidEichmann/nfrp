
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

import Test.Tasty
import Test.Tasty.HUnit

import Data.Serialize (Serialize)
import Data.Dynamic
import qualified Data.Map as M
import GHC.Generics (Generic)
import NFRP
import qualified Data.Time as Time

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "lcTransaction"
    [
        -- testCase "Simple Listener" $ do
        --     let (_, changes) = lcTransaction lc updateLists
    ]