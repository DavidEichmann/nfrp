# Netowking as a base for FRP
# Header

This is a literate haskell file so we start with some imports etc.

> {-# LANGUAGE ExistentialQuantification #-}
> {-# LANGUAGE TypeInType #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE TypeFamilies #-}
> 
> module Networking where

# Intro

This document attempts to build a framework of networking ideas that can be built apon to implement a distributed FRP network. This assumes:

* Nodes are all trusted and never fail.
* Connections between nodes are (in practice TCP can be used here):
    * Inorder
    * reliable (no packet loss nor data corruption)
    * have an expected small (on the order of less than a second) but unbounded delay.

We are concerned with how messages can be used and interpreted. All messages simply state a true fact about the "environment" $\Gamma$. When a node n receives a message i.e. a fact, they trust the sender node and add that fact to their knowlage base $\Sigma$. A node x for example can inform all other nodes that x0="Hello from x" by broadcasting that fact to all other nodes. It is important that nodes do not generate contradictory facts, but this can be solved by designating an "owner" of a variable in another variable $\omega_x$ for variable $x$. We'll need some place to start, so some rule must be hard coded into all nodes e.g. $\omega_genesis = NodeA$:

    Node n can assign variable $x$ iff $\omega_genesis = n$.

Implicitely, if a variable $\omega_x$ is not assigned, then it has no owner. It, and its corresponding variable can only be assigned by indering it from known facts.

## Time

Note that "variables" are immutable in the above scenario, but we can simulate mutable variables by using time-indexed variables. We likely choose to not time index correspoinding ownership variables (implying that the owner node is free to assign to a variable at all times).

We assume nodes have synchronized clocks. But these clocks should *only* be used to decide on new variable assignemt times. Dependant variables must change in 0 time! That is, when a node calculates a dependant value that it owns, it must do so for the time the value theoretically changed, and ignore the time it takes to calculate the dependant value.

## Infering Timely Facts

In an FRP setting, we usually want to infer a fact f at time t, that depends on the complete history of time indexed-variable x. How does a node know if the knowlage is complete?

    * If the local node owns the variable, then knowlage is complete.
    * else
        * We must design the protocol to ensure that complete information is received.
        * May need to send "heartbeats" to notify of no change.

# Static graph of behaviors

lets simplify and rely only on Behaviors, describing behaviors in terms of events

>