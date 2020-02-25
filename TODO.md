# TODO

* Naive NFRP: broadcast all source events
  * [X] Assume a single source event for all nodes. And create a function that
    generates all source events connected: my source event and also all other
    nodes' source events connected via TCP.
    * No clock sync (just have a placeholder)
  * [ ] Blog post
    * Why networking is hard
    * how unity 3D does networking
      * BONUS demonstrate shortcomings
        * There is local state and host state. These may not be in sync, and you may get race conditions if you combine local state with "sync vars". e.g. send command to host, then immediatelly read sync var and do some logic. Oooops sync var was not updated yet. Bam! Race condition!
        * Authoritative server -> double the lag compared to distributed.
  * [ ] (Tuesday) Create a test "Game" from circles demonstrating lack of race conditions
    * Simulate send delays (random)
    * split Game into 2 behaviors so you don't block current position
    * Shoot toward opposite position gives you a point if other player is there
    * Show score
    * BONUS show projectile when you shoot
    * create a bot that very quickly flips between 2 spots
    * show that even with a lot of lag both nodes calculate the same score
* [ ] UDP!
* [ ]
* [ ]
* [ ]
* [ ]

# Future work

* Vector clocks (and no clock synchronization)