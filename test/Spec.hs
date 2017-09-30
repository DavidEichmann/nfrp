
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
import qualified Data.Set as S
import GHC.Generics (Generic)
import Lib

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Description"
    [ testGroup "applyUpdates"    
        [ testGroup "empty update" $ assertApplyUpdates
            stepperCircuit
            []
            []
            []
        , testGroup "update: loneIntE=10" $ assertApplyUpdates
            stepperCircuit
            [gateUpdate loneIntE 10]
            [gateUpdate loneIntB 10]
            [gateUpdate loneIntE 10]
        ]
    ]

assertApplyUpdates
    :: Circuit node     -- ^ circuit
    -> [GateUpdate]     -- ^ updates
    -> [GateUpdate]     -- ^ expected behavior changes
    -> [GateUpdate]     -- ^ expected events
    -> [TestTree]
assertApplyUpdates circuit updates expectedBehaviorChangesList expectedEventsList =
    [ testCase "Changed Behaviors (Key)" $ M.keysSet behaviorChanges @?= expectedBehaviorChangesKeys
    , testCase "Events (Key)" $ M.keysSet events @?= expectedEventsKeys
    , testCase "Changed Behaviors (Value)" $ True @=? all
        (\update -> case update of
            GateUpdate key expectedValue -> expectedValue `eqDyn` (behaviorChanges M.! GateKey' key))
        expectedBehaviorChangesList
    , testCase "Events (Value)" $ True @=? all
        (\update -> case update of
            GateUpdate key' expectedValue -> expectedValue `eqDyn` (events M.! GateKey' key'))
        expectedEventsList
    ]
    where
        (_, behaviorChanges, events) = applyUpdates circuit updates
        expectedBehaviorChangesKeys = S.fromList [GateKey' key | GateUpdate key _ <- expectedBehaviorChangesList]
        expectedEventsKeys = S.fromList [GateKey' key | GateUpdate key _ <- expectedEventsList]



dynEqDyn :: forall a. (Typeable a, Eq a) => Dynamic -> Dynamic -> Bool
dynEqDyn d1 d2 = case (fromDynamic @a d1, fromDynamic @a d2) of
    (Just v1, Just v2) -> v1 == v2
    _ -> False

eqDyn :: forall a. (Typeable a, Eq a) => a -> Dynamic -> Bool
eqDyn v d = fromDynamic d == Just v

data LoneNode = LoneNode deriving (Generic, Serialize, Show, Eq, Ord)

stepperCircuit :: Circuit LoneNode  
((loneIntE, loneIntB), stepperCircuit) = mkCircuit $
    -- Define inputs
    do
    (intE :: E Int) <- localE LoneNode
    (intB :: B Int) <- stepper 0 intE
    -- return observations
    return (intE , intB)