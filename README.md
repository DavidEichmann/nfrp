# Networked Functional Reactive Programming (NFRP)

Describe interactive programs using FRP constructs and let NFRP handle all the networking.


## Awesome things (mostly TODOs :-P about this system)

* Networked FRP
    * No More data races ever!
* Parallel computation
* arbitrary time delays
* Time delay to infinity!
    * Usefull if you know a behaviour will be constant at some point and you want to ask what the final value is though it's a bit subtle: it will only work if your input behavior becomes evaluated at infinity. If it is e.g. a stepped behavior and you just filter the input event, and you know no more events will get through, The derived behavior wont really know that. If you have some constructs that just crop the behavior and set avalue till infinity, then that would work.
* Simple implementation means GC can go to town on the internal data structures! If we only try to observe the latest values, then we'll only hole references to the tip of the internal structure. The rest can be GC'd... of course we'd have to be carefull here, any reference to the original behavior will keep it and all dependant gates' full history alive!


## Motivation

Network programming is hard! Even when building upon reliable protocols like TCP, network latency is always an issue. As a result, the timing and ordering of events observed in a network will differ from node to node. Ideally we want to be able to reason in terms of some globally correct state, but this is hard to do when timing/ordering is inconsistent. One solution is to use a Client-Server model where the server defines the global correct state and the clients are simply informed of updates. This is simple, but also means that all network packages must pass through that server, potentially doubling latency. A more distributed model could send messages directly between nodes, avoiding the extra latency, but it seems much harder to reason about a global correct state. NFRP aims at the distributed model while letting you easily reason about a global correct state.

# Example

A simple example can be found in src/SumExample.cs. The example uses 2 nodes. Each inputs an integer and a sum is computed. can be built using ```stack build``` and run using:

```
# On Node A
stack exec Main -- NodeB <NodeB's address>

# On Node B
stack exec Main -- NodeA <NodeA's address>

# OR run all nodes localy.
stack exec Main
```

The code to describe the circuit is actually quite simple:

```Haskell
-- |The network consists of two nodes.
data Node
  = NodeA
  | NodeB
  deriving (Generic, Serialize, Show, Read, Eq, Ord, Bounded, Enum)

-- |NFRP circuit takes an Int from each node and sums them.
sumCircuit :: Circuit Node
-- |Event sink for changes to nodeA's Int.
nodeAIntESink :: E Int
-- |Event sink for changes to nodeB's Int.
nodeBIntESink :: E Int
-- |Behavior of node A's Int.
nodeAIntB :: B Int
-- |Behavior of node B's Int.
nodeBIntB :: B Int
-- |Behavior of the sum of both nodes' Ints.
sumB :: B Int
((nodeAIntESink, nodeBIntESink, nodeAIntB, nodeBIntB, sumB), sumCircuit) =
  mkCircuit $
   do
    -- |Event sourced from NodeA
    nodeAIntESink' <- localE NodeA
     -- |Event sourced from NodeB
    nodeBIntESink' <- localE NodeB
    -- Convert to behaviors (initially set to 0).
    nodeAIntB' <- stepper 0 nodeAIntESink'
    nodeBIntB' <- stepper 0 nodeBIntESink'
    -- Sum the nodeA and nodeB ints.
    sumB' <- liftB2 (+) nodeAIntB' nodeBIntB'
    -- return events and behaviors.
    return
      ( nodeAIntESink'
      , nodeBIntESink'
      , nodeAIntB'
      , nodeBIntB'
      , sumB')
```

# How

All nodes engage in clock synchronization and time stamp all messages sent over the network, allowing for a global ordering of messages. Once all messages stamped before a time ```t``` are received by a node, it can progress the program up to time t and be certain that it represents the global correct state. Due to latency, ```t``` will always be a bit before the current time. Because the structure and semantics of an FRP program are visible to NFRP, the entire state of the program can easily be tracked and rolled back. This allows NFRP to progress past time ```t``` to estimate the current state, then rollback and correct itself as new messages are observed.

# Progress

This is still very early and experimental. What I've done and wan to do:

- [X] Stateless FRP constructs.
- [X] Simple Clock Synchronization.
- [X] TCP based messaging.
- [ ] Rollback/Replay (This should be easy).
- [ ] Stateful FRP constructs (allow the ability to refer to the previous state).
- [ ] Better Clock Synchronization (Perhaps using moving average and accounting for clock drift).
- [ ] Account for floating point (non)determinism.
- [ ] Improve ergonomics.
- [ ] Control over which Behaviors/Events to broadcast. At the moment NFRP reduces to simply broadcasting all inputs (event sinks declared with ```localE```). This is an important non-trivial feature.
- [ ] Custom prediction methods (client-side prediction): Allow the programmer e.g. predict the current value of a Behavior based on the latest correct global state.
- [ ] UDP based messaging.
- [ ] Interface with "local" systems (e.g. a physics system) with custom work distribution.
