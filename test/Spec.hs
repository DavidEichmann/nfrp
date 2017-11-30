
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
import Lib
import qualified Data.Time as Time

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Description"
    [ testGroup "applyUpdates"
        [ testGroup "stepperCircuit"
            [ testGroup "empty update" $ assertApplyUpdates
                stepperCircuit
                [([], [NoChange stepperIntB], [NoOccurence stepperIntE])]
            , testGroup "update: stepperIntE=10" $ assertApplyUpdates
                stepperCircuit
                [([gateUpdate stepperIntE 10], [Change stepperIntB 10], [Occurence stepperIntE 10])]
            ]
        , testGroup "sumCircuit" $ assertApplyUpdates
            sumCircuit
            [ ( [GateUpdate sumClientIntE 11, GateUpdate sumServerIntE 2200]
                , [Change sumSumB 2211]
                , [Occurence sumClientIntE 11, Occurence sumServerIntE 2200]
                )
            , ( [GateUpdate sumClientIntE 109]
                , [Change sumSumB 2309]
                , [Occurence sumClientIntE 109, NoOccurence sumServerIntE]
                )
            ]
        , testGroup "sumCircuit with encode/decode transactions" $ assertApplyUpdatesTransactionRoundTrip
            sumCircuit
            [ ( [GateUpdate sumClientIntE 11, GateUpdate sumServerIntE 2200]
                , [Change sumSumB 2211]
                , [Occurence sumClientIntE 11, Occurence sumServerIntE 2200]
                )
            , ( [GateUpdate sumClientIntE 109]
                , [Change sumSumB 2309]
                , [Occurence sumClientIntE 109, NoOccurence sumServerIntE]
                )
            ]
        ]
    ]

data ExpectedBehaviorChange
    = forall a. GateValue a => NoChange (B a)
    | forall a. GateValue a => Change (B a) a

data ExpectedEventOccurence
    = forall a. GateValue a => NoOccurence (E a)
    | forall a. GateValue a => Occurence (E a) a

assertApplyUpdatesTransactionRoundTrip
    :: Circuit node     -- ^ circuit
    -> [([GateUpdate]     -- ^ updates
        , [ExpectedBehaviorChange]     -- ^ (subset of) expected behavior changes
        , [ExpectedEventOccurence])]     -- ^ (subset of) expected events
    -> [TestTree]
assertApplyUpdatesTransactionRoundTrip _ [] = []
assertApplyUpdatesTransactionRoundTrip circuit ((updates, expectedBehaviorChangesList, expectedEventsList):xs)
    = let
    time = Time.UTCTime (Time.fromGregorian 1 1 1) 0
    Right (Transaction timeCopy updatesRoundTrip) = decodeTransaction circuit . encodeTransaction $ Transaction time updates
    (circuit', currentTests) = assertApplyUpdates1 circuit updatesRoundTrip expectedBehaviorChangesList expectedEventsList
    assertTime = testCase "Time decoded correctly" (timeCopy @=? time)
    in currentTests ++ (assertTime : assertApplyUpdatesTransactionRoundTrip circuit' xs)

assertApplyUpdates
    :: Circuit node     -- ^ circuit
    -> [([GateUpdate]     -- ^ updates
        , [ExpectedBehaviorChange]     -- ^ (subset of) expected behavior changes
        , [ExpectedEventOccurence])]     -- ^ (subset of) expected events
    -> [TestTree]
assertApplyUpdates _ [] = []
assertApplyUpdates circuit ((updates, expectedBehaviorChangesList, expectedEventsList):xs) = let
    (circuit', currentTests) = assertApplyUpdates1 circuit updates expectedBehaviorChangesList expectedEventsList
    in currentTests ++ assertApplyUpdates circuit' xs

assertApplyUpdates1
    :: Circuit node     -- ^ circuit
    -> [GateUpdate]     -- ^ updates
    -> [ExpectedBehaviorChange]     -- ^ (subset of) expected behavior changes
    -> [ExpectedEventOccurence]     -- ^ (subset of) expected events
    -> (Circuit node, [TestTree])
assertApplyUpdates1 circuit updates expectedBehaviorChangesList expectedEventsList =
    ( circuit'
    , [ testCase "Behaviors" $ True @=? all
            (\update -> case update of
                NoChange key
                    -> not (GateKey' key `M.member` behaviorChanges)
                Change key expectedValue
                    -> expectedValue `eqDyn` (behaviorChanges M.! GateKey' key))
            expectedBehaviorChangesList
        , testCase "Events" $ True @=? all
            (\update -> case update of
                NoOccurence key
                    -> not (GateKey' key `M.member` events)
                Occurence key expectedValue
                    -> expectedValue `eqDyn` (events M.! GateKey' key))
            expectedEventsList
    ])
    where
        (circuit', behaviorChanges, events) = applyUpdates circuit updates



dynEqDyn :: forall a. (Typeable a, Eq a) => Dynamic -> Dynamic -> Bool
dynEqDyn d1 d2 = case (fromDynamic @a d1, fromDynamic @a d2) of
    (Just v1, Just v2) -> v1 == v2
    _ -> False

eqDyn :: forall a. (Typeable a, Eq a) => a -> Dynamic -> Bool
eqDyn v d = fromDynamic d == Just v

data LoneNode = LoneNode deriving (Generic, Serialize, Show, Eq, Ord)

stepperCircuit :: Circuit LoneNode
stepperIntE :: E Int
stepperIntB :: B Int
((stepperIntE, stepperIntB), stepperCircuit) = mkCircuit $
    -- Define inputs
    do
    (intE :: E Int) <- localE LoneNode
    (intB :: B Int) <- stepper 0 intE
    -- return observations
    return (intE , intB)

data CSNode = Client | Server deriving (Generic, Serialize, Show, Eq, Ord)

sumCircuit :: Circuit CSNode
sumClientIntE :: E Int
sumServerIntE :: E Int
sumSumB :: B Int
((sumClientIntE, sumServerIntE, sumSumB), sumCircuit) = mkCircuit $ do
    clientIntE <- localE Client
    serverIntE <- localE Server
    serverIntB <- stepper 0 serverIntE
    clientIntB <- stepper 0 clientIntE
    sumB <- liftB2 (+) serverIntB clientIntB
    return
        ( clientIntE
        , serverIntE
        , sumB
        )
