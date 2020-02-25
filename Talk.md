* I've made an FRP library
    * Behavior and Event types
        * Total (for all time)
    * example with `step` and `(+) <$> a <*> b` and `behaviourToList`
* Circles example
    * Code
        * ask/stress how simple the code is
    * run it
* Representation of Event/Behavior.
    * Converting EventParts into Event
    * `sourceEvent`
* `WatchB` + apology for abusing GHC
* We have Behavior->parts and parts->behavior
    * order is unimportant to semantics (only affects when data becomes available)
    * naive networking!
    * `sourceEvents`


* Circles example again
    * It is actually networked already.
    * Don't get to excited.
        * naive "send-all-inputs" approach
* Context
    * gafferongames.com
        * "What Every Programmer Needs To Know About Game Networking"
            * 2010 - Old but still applicable
            * 2 models:
                * "P2P Lockstep"
                    * Mechanism:
                        * Fully connected network topo.
                        * Send just inputs
                        * Everyone runs deterministic simulations
                    * pros:
                        * elegant
                        * low bandwidth
                    * cons:
                        * requires determinism
                        * Wait for ALL players
                            * lag = slowest player's lag
                        * All players must start from same initial state
                    * Used in
                        * Doom
                        * RTS games
                * Client/Server
                    * First developed in Quake
                    * Mechanism
                        * Server is the ground truth!
                        * network topo. only Clients<->Server

                        * Interpolation (of e.g. positions of other players)
                        * client-side prediction
                            * reconciliation
                    * pros:
                        * security
                        * "no lag"
                            * for your character
                    * cons:
                        * Lag
                            * when it's most important: player to player interaction

    * BONUS Unity3D (Client/Server)
        * Server Authoritative
        * SyncVar
        * Command + Rpc

* Use P2P to reduce lag and fix all the cons in P2P cons:
    * security
        * can still check for cheaters (just not in real time)
    * requires determinism
        * Only relevant to "send just inputs"
    * Wait for ALL players
        * Only relevant to "send just inputs"/determinism
    * All players must start from same initial state

