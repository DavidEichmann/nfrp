{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}

module Theory where

    import Unsafe.Coerce
    import Data.Kind
    import Data.List (find)
    import Data.Maybe (isJust)

    import Time
    import KnowledgeBase.Timeline (FactSpan (..))
    import TimeSpan

{-
# NFRP Introduction

NFRP is a networked FRP system. In practice we know when events are happening
(and not happening) only for explicit spans of time. As we observe inputs from
users and share information over the internet, our knowledge strictly increases.

TODO talk about how we use total semantics as a mental model when using NFRP,
but use the partial semantics for implementation (and I guess we might use it
for more complicated aspect of NFRP like how to observe/listen to
events/behaviors). Also, all the partial semantics functions should always
either give Unknown or a value consistent with the total semantics.

## Events Intro

The main abstraction we use to model programs is an "Event". An event is
something that occurs at distinct and instantaneous points in time. Each event
occurrence may also carry with it a piece of data. While not used in this form
in NFRP it is helpful to think of a (total) Event as the following datatype:

    type Event a = [(Time, a)]

    type Time = Double

Note that the times in the Event's list are the event occurrence times, and must
all be distinct i.e. an event can only be occurring at most once fr any given
time. In practice we don't represent events like this, instead we index them
using an event index type:
-}
    newtype EIx (a :: Type) = EIx Int
        deriving newtype Eq
{-
For example `EIx 100` might refer to the event for a right mouse click, and `EIx
101` might refer to the event for a left mouse click. We then use the index to
lookup knowledge in a `knowledgeBase`.

## KnowledgeBase

Our knowledge is only ever partial. We can think of our current knowledge as a
set of known facts about events:
-}
    -- | A set (actually a list) of known facts.
    data KnowledgeBase = KnowledgeBase [SomeFact]

    -- | A knowledge base with no facts.
    emptyKnowledgeBase :: KnowledgeBase
    emptyKnowledgeBase = KnowledgeBase []

    -- | A fact for some arbitrary event of type `a`.
    data SomeFact = forall a . SomeFact (EIx a) (Fact a)

    -- | `Just x` mean the event is occurring with the value `x`. Nothing means
    -- the event is not occurring.
    type MaybeOcc a = Maybe a

    -- | A single fact about an event.
    data Fact a
        = NoOcc SpanExc           -- No event is occurring in this time span.
        | Occ Time (MaybeOcc a)   -- A single event may be occurring at this time.

    -- | `SpanExc lo hi` is a time span from `lo` to `hi` excluding `lo` and
    -- `hi`. If `lo` or `hi` is Nothing, that indicates an open interval. e.g.
    --
    --      SpanExc (Just 1) (Just 5)  means  1 < t < 5
    --      SpanExc Nothing  (Just 5)  means      t < 5
    --      SpanExc (Just 1) Nothing   means  1 < t
    --      SpanExc Nothing Nothing    means "all time"
    --
    -- TODO this is Defined in the TimeSpan module
{-
Importantly, all facts are qualified over a point or span of time, and hence
will never become untrue. There is a fairly intuitive reason why this is useful.
The statement "The user is clicking the left mouse button" may be true now but
will be untrue a moment later. In contrast, if we qualify the time, this
statement will always be true: "The user clicked the left mouse button at
exactly 6:30AM". Time travel is out of the scope of NFRP. We can now ask: what
are all the known facts for a given event?
-}
    factsE :: EIx a -> KnowledgeBase -> [Fact a]
    factsE (EIx eix) (KnowledgeBase es)
        = [ unsafeCoerce fact
            | SomeFact (EIx eix') fact <- es
            , eix == eix'
            ]
{-
More fundamentally, we can also ask: is an event occurring at a given time:
-}
    type MaybeKnown a = Maybe a

    lookupE :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
    lookupE time eix kb = case find (\fact -> toFactSpan fact `contains` time) (factsE eix kb) of
        Just (NoOcc _)    -> Just Nothing
        Just (Occ _ aMay) -> Just aMay
        Nothing           -> Nothing
{-
Remember we only have partial knowledge so the result is one of:

    `Nothing`        meaning  "Unknown!"
    `Just Nothing`   meaning  "Known! The event is NOT occurring"
    `Just (Just x)`  meaning  "Known! The event IS occurring with value `x`"

### Derived Events

When modeling our reactive program in FRP we wan to be able to define derived
events in terms of other events. For this we need some language to describe
derived events. For this NFRP provides a monadic interface (TODO why use the
total denotation here?)
-}
    -- | Using the total denotation throughout
    -- [[ EventM a ]]  =  [[ Event a ]]      -- Some event occurrences
    data EventM a
        -- TODO this definition is a bit cheating because we use Pure... actually the denotation is either a pure value or a event occ list.
        -- [[ GetE eix f ]]
        --      = -- when eix IS occurring
        --         [ case f (Just b) of
        --               Pure a -> (t, a)
        --               aM -> [ (t, a) | (t', a) <- [[ aM ]], t' == t ]
        --           | (t , b) <- eventOccs eix
        --           ]
        --        -- when eix is NOT occurring
        --         ++ case f Nothing of
        --                   Pure a -> []
        --                   aM -> [ (t, a)
        --                             | (t, a) <- [[ aM ]]
        --                             , not $ t `elem` (fst <$> eventOccs eix))
        --                             ]
        = forall b . GetE (EIx b) (MaybeOcc b -> EventM a)

        -- | A pure value
        -- [[ Pure a ]]  =  []
        | Pure a
        -- [[ ReturnNoOcc ]]  =  []
        | ReturnNoOcc

        -- [[ PreviousE eix f ]] = [ (ta, a)
        --    | (t, b, t') <- eventOccsAndNextOccTimeMay eix   -- nextOccTimeMay is Nothing for final event
        --    , (ta, a) <- [[ f (Just b) ]]
        --    , t < ta && maybe True (ta <=) t'
        --    ] ++
        --    -- Before first event
        --    (filter ((beforeFirstOccTime eix <) . fst) [[ f Nothing ]])
        | forall b . LatestE   (EIx b) (Maybe b -> EventM a)
        | forall b . PreviousE (EIx b) (Maybe b -> EventM a)

    deriving instance Functor EventM

    -- | Optionally require this event. In order for the resulting event to
    -- occur, at least 1 of all `getE`ed events must be occurring.
    getE :: EIx a -> EventM (MaybeOcc a)
    getE eix = GetE eix (maybe (Pure Nothing) (Pure . Just))

    -- | We can derive a variant of getE that requires the dependent event to
    -- be occurring.
    requireE :: EIx a -> EventM a
    requireE eix = do
        depMay <- getE eix
        case depMay of
            Nothing -> ReturnNoOcc
            Just a -> return a
{-
Ok well now we have some kinda confusing ass monad, but I imagine the usage to
feel a lot more natural. Also, it's starting to look like the naive
implementation will not terminate because we'll be forcing whole lists of event
occurrences which will clearly not work (it forces future events!).


TODO

I think it may be nicer to use `Time -> MaybeOcc a` as a denotation of Events.

For a simple self reference, you should be able to prove mathematically
from the EventM denotations something along the lines of "you can assume there
are no events happening as long as all other (i.e. non self referencing)
dependencies are not occurring". Then hopefully you can expand on that to show
how you can handle transitive self dependencies (and hopefully that's sufficient
for the programs will be modeling).
-}













{-

{-
## Background

### Semantics of Total Event

We use a continuous time type `Time`. In practice we use `Int64` representing
nanoseconds.

Consider an `Event a` this represents a stream of events happening at distinct
times. This is "total" in the sense that it is complete knowledge of all event
occurrences for all time. As is typical of FRP systems we have the following
denotation:

    ⟦ Event a ⟧ = [(Time, a)]   -- Where Time values are distinct.

Note that `⟦x⟧` means "denotation of x" and `[x]` is regular haskell syntax
meaning "a list of x". As the time values are distinct, this means that at any
point in time an event is occurring either exactly once or not at all. We can
now answer the question of "is an event occurring at a given time?":
-}
    type MaybeOcc a = Maybe a
{-
    lookupTotalE :: Time -> Event a -> MaybeOcc a
    lookupTotalE = lookup

This is a clear and simple denotation, and is ultimately the mental model users
of the NFRP library will use when writing the logic of their program. When it
comes to implementation of NFRP a richer denotation will be used.

## KnowledgeBase

In practice we only ever have partial knowledge that evolves as the program
runs, receives new inputs, and communicates with other "nodes" over a network.
Hence, when considering implementation, we make use of a `KnowledgeBase`. We
also refer to Events with an event index.
-}
    newtype EIx (a :: Type) = EIx Int         -- Index of an event

    data SomeFact = forall a . SomeFact (EIx a) (Fact a)

    data KnowledgeBase = KnowledgeBase [SomeFact]

    emptyKnowledgeBase :: KnowledgeBase
    emptyKnowledgeBase = KnowledgeBase []

    factsE :: EIx a -> KnowledgeBase -> [Fact a]
    factsE (EIx eix) (KnowledgeBase es)
        = [ unsafeCoerce fact
            | SomeFact (EIx eix') fact <- es
            , eix == eix'
            ]
{-
That represents the current knowledge of a set of events (and later also
behaviors). As we receive new facts, we can add them to the `KnowledgeBase`:

    insertFact :: SomeFact -> KnowledgeBase -> KnowledgeBase
    insertFact = ...

This isn't as simple as appending facts to the list of facts as we also want to
derive knowledge from existing facts. How exactly we derive all this knowledge
is a main source of complexity when implementing NFRP.

# Semantics of (Partial) Event

Throughout the implementation of NFRP we always think of events as partial i.e.
we only have knowledge of events for explicit periods of time. We make partial
knowledge explicit with the following denotation:

    ⟦Event a⟧ = (Time -> MaybeKnown (MaybeOcc a))

        -- Where Occurrences happen at distinct times i.e. have 0 duration.

The representation we use is:
    newtype Event a = Event [Fact a]
-}
    data Fact a
        = NoOcc SpanExc        -- No event is occurring in this time span.
        | Occ Time (Maybe a)   -- A single event may be occurring at this time.
{-
So now not only do we store the event occurrences (`Occ Time a` or in the
old denotation `(Time, a)`), but we also store the spans of time where we know
there are no event occurrences, `NoOcc SpanExc`. All time not covered by
these facts is implicitly "unknown". Now our `lookupE` function changes a bit:
-}
    type MaybeKnown a = Maybe a

    lookupE :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
    lookupE time eix kb = case find (\fact -> toFactSpan fact `contains` time) (factsE eix kb) of
        Just (NoOcc _)    -> Just Nothing
        Just (Occ _ aMay) -> Just aMay
        Nothing           -> Nothing

    isOccurring :: Time -> EIx a -> KnowledgeBase -> MaybeKnown Bool
    isOccurring time eix kb = fmap isJust (lookupE time eix kb)

    toFactSpan :: Fact a -> FactSpan
    toFactSpan (NoOcc tspan) = FS_Span tspan
    toFactSpan (Occ t _) = FS_Point t
{-
## Source and Derived Events

Now that we have a denotation/representation for events, we can easily construct
events directly like so:

    -- An event that never occurs.
    e1 = Event [NoOcc (spanExc Nothing Nothing)]

    -- An event that occurs at time 10 and unknown at and after time 100.
    e1 = Event
            [ NoOcc (spanExc Nothing (Just 10))
            , Occ 10 "Hi, I'm an event occurrence at time 10"
            , NoOcc (spanExc (Just 10) (Just 100))
            ]

This method of constructing events is how we'll ultimately express the input
events to our program. We'll call these input events "source events". In a large
program, we expect there to only be a small set of input events compared to the
total number of events we want to describe. In the context of a video game, we
may only have a single source event `Event PlayerInputs` from which the entire
game logic will be derived. So we need a way to create "derived events" from
other events. NFRP provides a Monadic interface for this. The *Monadic* part is
a key feature distinguishing NFRP from other FRP libraries. A key advantage to
the monadic style is that it makes "switching" very natural (`switch` is just
`join`).

The `EventM` monad is used to describe a derived event:
-}

    data EventM a
        = forall b . GetE (EIx b) (MaybeOcc b -> EventM a)
        -- ^ Mark the EIx as a
        | Pure a
        | ReturnNoOcc
        -- These are explained in the next section.
        | forall b . LatestE   (EIx b) (Maybe b -> EventM a)
        | forall b . PreviousE (EIx b) (Maybe b -> EventM a)

    deriving instance Functor EventM

    -- | Optionally require this event. In order for the resulting event to
    -- occur, at least 1 of all `getE`ed events must be occurring.
    getE :: EIx a -> EventM (MaybeOcc a)
    getE eix = GetE eix (maybe (Pure Nothing) (Pure . Just))
{-
The interpretation can be summed up in this function:
-}

    -- TODO support self reference (will require adding a "self" `EIx a` parameter)
    lookupEM :: Time -> EventM a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
    lookupEM _ (Pure _) _ = Just Nothing -- Do dependent events, so the resulting event never occurs.
    lookupEM t top kb = go top
        where
        go :: EventM a -> MaybeKnown (MaybeOcc a)
        go (GetE depEIx cont) = _
        go (Pure a) = _
        go ReturnNoOcc = _
        go (LatestE   depEIx cont) = _
        go (PreviousE depEIx cont) = _

    -- | We can derive a variant of getE here
    requireE :: EIx a -> EventM a
    requireE eix = do
        depMay <- getE eix
        case depMay of
            Nothing -> ReturnNoOcc
            Just a -> return a

{-
So the event expressed by a `EventM` withe index `eix` has the following
property. Given `getE` dependencies, gDeps, and `requireE` dependencies, rDeps,
and assuming a Time and KnowledgeBase:

    isOccurring eix  <->  any isOccurring gDeps     (null rDeps)
                          all isOccurring rDeps     (otherwise)

Note that this implies that if `(null rDeps && null gDeps)` then the `eix` event
NEVER occurs. Also note that since this is monadic, `gDeps` and `rDeps` may
depend on the values of previous dependencies. Here is an example of a game over
event for some imagined 2 player game:

    -- player1DeadE, player2DeadE :: EIx ()

    do
        player1DeadMay <- getE player1DeadE
        player2DeadMay <- getE player2DeadE
        case (player1DeadMay, player2DeadMay) of
            (Just (), Nothing) -> return (Just "Player 2 wins!")
            (Nothing, Just ()) -> return (Just "Player 1 wins!")
            (Just (), Just ()) -> return (Just "It's a tie!")
            (Nothing, Nothing)
                -> error "Impossible! At least one of the getE events must be \
                         \occurring (since there are not requireE events)"

This event occurs when one of the players dies, and also handles the case of
both players dieing at the same time. Having to handle the `(Nothing, Nothing)`
is a bit unfortunate, but I can't see much of a way around this.

Here is another example for a multiplayer game with possibly many winners. This
event occurs at the end of the game if player 1 died at exactly the end of the
game.

    -- endOfGameE :: EIx ()

    do
        requireE endOfGameE
        player1DeadMay <- getE player1DeadE
        case player1DeadMay of
            Nothing -> return Nothing
            Just () -> return (Just "Player 1 died at the end of the game")
-}
{-

## Latest / Previous Event value.

Another way at query an event is to consider that latest or previous event
occurrence. That is the latest event occurrence at any given time. This is
partial as such a value doesn't exits until at/after the first event occurrence.
-}

    -- NOTE these have to ensure we have complete knowledge from the
    -- latest/previous occurrence till the target time.

    latestE :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (Maybe a)
    latestE = error "TODO latestE"

    previousE :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (Maybe a)
    previousE = error "TODO previousE"
{-
### State

Before the addition of latestE/previousE, there was no way to access old state.
Indeed, without these functions, events are entirely stateless and can be fully
derived from the current time's source events. latestE/previousE allow us to
look back in time and introduce an evolving state. Here is an example where we
simply count the number of times another event occurs.

    -- otherEvent :: EIx ()

    -- countE :: EIx Int
    -- TODO initially 0
    do
        requireE otherEvent
        currentCount <- previousE countE
        return (Just (currentCount + 1))



## Problematic case

These 2 are actually semantically the same:

    aE = event $ do
        requireE otherEvent
        currentCount <- previousE aE
        return (Just (currentCount + 1))

    bE = event $ do
        _ <- getE otherEvent
        currentCount <- previousE countE
        return (Just (currentCount + 1))

But the `getE` causes a deadlock with a naive implementation. That's because of
the self reference. Imagine we have these source facts:

    otherEventFacts
        = [ NoOcc (spanExc Nothing (Just 10))
          , Occ 10 ()
          ]

We should be able to derive these facts:

    aE facts = bE facts
        = [ NoOcc (spanExc Nothing (Just 10))
          , Occ 10 1
          ]

In case A we'll succeed in deriving this because the EventM short circuits when
seeing otherEvent's NoOcc, and immediatelly gives NoOcc for A from time NegInf
to 10. In B, after seeing the NoOcc of otherEvent, we can't short circuit
because we've used `getE`. Instead we move to the next dependency which is a
self dependency. Deadlock!

It is tempting to try and solve this problem by somehow identifying and managing
self dependencies, but the problem is more general. Consider what happens when I
split bE into multiple events. There are no self references, only indirect self
references:

    aE = event $ do
        _ <- getE otherEvent
        currentCount <- previousE dE
        return (Just (currentCount + 1))

    bE = event $ getE aE
    cE = event $ getE aE

    dE = event $ do
        bMay <- getE bE
        cMay <- getE cE
        return (bMay <|> cMay)

How can we possibly make progress here (i.e. produce facts)?

My *intuition* says that if a set of running EventMs over a common time span
depend on each others' output (i.e. form a transitive closure), then... then
what? Well then we have a deadlock. For spans (not points) of time where we know
that it must start with a NoOcc span (either a subset or equal to the larger
span), we just don't know when the span will end. It ends at the next closest (in time) event occurence



-}
-}
{- APPENDIX -}

    -- TODO

    instance Applicative EventM where
    instance Monad EventM where