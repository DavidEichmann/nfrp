# Networked Functional Reactive Programming (NFRP)

Describe interactive programs using FRP constructs and let NFRP handle all the networking.

## Motivation

Network programming is hard! Even when building upon reliable protocols like TCP, network latency is always an issue. As a result, the timing and ordering of events observed in a network will differ from node to node. Ideally we wan to be able to reason in terms of some globally correct state, but this is hard to do when timing/ordering is inconsisten. One solution is to use a Client-Server model where the server defines the global correct state and the clients are simply informed of updates. This is simple, but also means that all network packages must pass throught that server, potentially doubling latancy. A more distributed model could send messages directly between nodes, avoiding the extra latency, but it seems much harder to reason about a global correct state. NFRP aims at the distributed model while letting you easily reason about a global correct state.

# Example

See SumExample.hs

# How

All nodes engage in clock synchronization and time stamp all messages sent over the network, allowing for a global ordering of messages. Once all messages stamped before a time ```t``` are received by a node, it can progress the program up to time t and be certain that it represents the global correct state. Due to latency, ```t``` will always be a bit before the current time. Because the structure and semantics of an FRP program are visible to NFRP, the entire state of the program can easily be tracked and rolled back. This allows NFRP to progress past time ```t``` to estimate the current state, then rollback and correct itself as new messages are observed.

# Progress

This is still very early and experimental. What I've done and wan to do:

- [X] Stateless FRP constructs.
- [X] Simple Clock Synchronization.
- [X] TCP based messaging.
- [ ] Rollback/Replay (This should be easy).
- [ ] Statefull FRP constructs (allow the ability to refer to the previous state).
- [ ] Better Clock Synchronization (Perhaps using moving average and accounting for clock drift).
- [ ] Account for floating point (non)determinism.
- [ ] Control over which Behaviors/Events to broadcast. At the moment NFRP reduces to simply broadcasting all inputs (event sinks declared with ```localE```). This is an important non-trivial feature.
- [ ] Custom prediction methods (client-side prediction): Allow the programmer e.g. predict the current value of a Behavior based on the latest correct global state.
- [ ] UDP based messaging.
- [ ] Interface with "local" systems (e.g. a physics system) with custom work distribution.
