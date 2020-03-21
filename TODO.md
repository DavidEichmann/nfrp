# TODO

* 2 important issues:

  1. WTF are actually the semantics of the Rule monad? It's odd that we can just
     arbitrarily combine events and behaviors (current and next). So let's
     define them better.

     Just like we can think of Events as a Behavior of Maybe a value, we can
     also think of Behaviors as an initial value and an Event (i.e. the changes
     to the value). We can then say the current value of a behavior is the
     latest event strictly before the current time, and the next value is the
     latest event before or equal to the current time.

     So at least in terms of semantics, we can stick to thinking about events
     and "latest"/"previous" occurrences given some initial value.

     So what does it mean to getE in a Rule. I think each getE will return Maybe
     the event occurrence implying that we are "merging" events i.e. the
     resulting event will occur when any of the getE events occur. We can also
     provide a `requireE` which will short circuit: the resulting event will
     only happen when the required event happens. If multiple events are
     required, then the resulting event will occur only when all the required
     events are occuring. Note that the `requiredE` event completely override
     the `getE` events in terms of the resulting event's occurrences:

        result event occurs  <->  if any requiredE events
                                    then (all requiredE events are occuring)
                                    else (any getE events are occuring)

    With a `getLatestE, getPreviousE :: EIx a -> Rule (Maybe a)`

  2. How the hell do we resolve dead lock?

      * Originally I thought this was an issue with self references, but the
        problem is more general! It has to do with the fact that Rules are
        monadic, so we can't progress / produce knowledge. My intuition is that
        for spans of time, we know that the start of the span (or the whole
        span) must be a NoChange span. Hence if we depend on a span that we
        don't yet have knowledge for, we can at least use the knowledge that it
        starts with a NoChange span to progress. The the catch is that we don't
        know when that span ends, so we'll need a way to deal with that.
        Specifically we'll need a way to express facts without knowing when they
        end.

            xE = NoChange till time T then unknown

            behaviorA = steppedB initA $ do
              xMay <- getE xE
              b    <- getB behaviorB
              return (f xMay b)

            behaviorB = steppedB initB $ do
              xMay <- getE xE
              a    <- getB behaviorA
              return (f xMay a)

        The above should NOT deadlock. By looking at this we know that behaviorA
        should have no change up to time T. Even though we behaviours A and B
        depend on eachother, they only depend on the *previous* value, so this
        should work out. Currently this does deadlock because the active rules
        will both be waiting on facts for the other behavior.

