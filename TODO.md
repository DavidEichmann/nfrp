# TODO

* Instead of distinguising between Time and SpanExc, just use Span
* An efficient implementation and a way to test it against the model
  implementation.
  * I think it should be easy enought to do model testing. Just need a way to
    generate some synthetic programs.
* An Event interface implemented in terms of the Value interface
* Given that we have the "idealized" algorithm, we now need to think about
  making this networked. I'm guessing this will involve a higherlevel API that
  allows you to define your Events/Value. This API will probably need to keep
  track of some extra info and use that to know what communication is needed
  between nodes.