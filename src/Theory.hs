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

    import qualified Control.Monad as M
    import Data.Kind
    import Data.List (foldl')
    import Data.Maybe (fromMaybe)
    import Unsafe.Coerce

    import Time
    -- import KnowledgeBase.Timeline (FactSpan (..))
    import TimeSpan

    data EventFact a
        = FactNoOcc SpanExc
        | FactMayOcc Time (MaybeOcc a)

-- We have some set of `EIx`s, 𝔼, and a definition for each: either a source
-- event or derived event and we want to calculate all facts about the derived
-- events from the source events.

    data InputEl = forall a . InputEl (EIx a) (Either [EventFact a] (EventM a))
    type Inputs = [InputEl]

    type MaybeOcc a = Maybe a

    newtype EIx (a :: Type) = EIx Int         -- Index of an event
        deriving newtype Eq

-- Derived events are expressed with the EventM monad:

    data EventM a
        = Pure a
        | NoOcc
        | forall b . GetE  (EIx b) (MaybeOcc b -> EventM a)
        | forall b . PrevE (EIx b) (Maybe    b -> EventM a)

    deriving instance Functor EventM

    instance Applicative EventM where
        (<*>) = M.ap
        pure = return

    instance Monad EventM where
        return = Pure
        fa >>= fmb = case fa of
            Pure a -> fmb a
            NoOcc -> NoOcc
            GetE  eixb mayOccToCont  -> GetE  eixb ((>>= fmb) . mayOccToCont)
            PrevE eixb mayPrevToCont -> PrevE eixb ((>>= fmb) . mayPrevToCont)

    getE :: EIx a -> EventM (MaybeOcc a)
    getE eix = GetE eix Pure

    prevE :: EIx a -> EventM (Maybe a)
    prevE eix = PrevE eix Pure

-- Give some `inputs :: Inputs`, we have this denotation for an event/EventM:

    -- lookupE :: Time -> EIx a -> MaybeOcc a
    -- lookupE t eix = case inputs eix of
    --     Left lookupSourceE -> lookupSourceE t
    --     Right eventM -> deriveE t eventM

    -- deriveE :: forall a . Inputs -> Time -> EventM a -> MaybeOcc a
    -- deriveE t eventM = deriveEgo False eventM
    --
    -- deriveEgo :: Time -> Bool -> EventM a -> MaybeOcc a
    -- deriveEgo t False (Pure _) = Nothing
    -- deriveEgo t True  (Pure a) = Just a
    -- deriveEgo t _     NoOcc    = Nothing
    -- deriveEgo t seenOcc (GetE eixB cont) = case lookupE inputs t eixB of
    --     Nothing -> deriveEgo t seenOcc (cont Nothing)
    --     Just b  -> deriveEgo t True    (cont (Just b))
    -- deriveEgo t seenOcc (PrevE eixB cont)
    --     = if ∃ t'  .  t' < t
    --                ∧  isJust (lookupE t' exiB)
    --                ∧  (∀ t' < t'' < t  .  lookupE t'' exiB == Nothing)
    --         then lookupE t' exiB
    --         else Nothing

-- We store a knowledge base:

    data SomeEventFact = forall a . SomeEventFact (EIx a) (EventFact a)
    data SomeDerivation = forall a . SomeDerivation (EIx a) (Derivation a)

    data KnowledgeBase = KnowledgeBase [SomeEventFact] [SomeDerivation]

    factsE :: EIx a -> KnowledgeBase -> [EventFact a]
    factsE (EIx eix) (KnowledgeBase es _)
        = [ unsafeCoerce fact
            | SomeEventFact (EIx eix') fact <- es
            , eix == eix'
            ]

-- A derivation is a partial evaluation of the `deriveE` function, universally
-- quantified over a range of time.

    startDerivationForAllTime :: EventM a -> Derivation a
    startDerivationForAllTime em = KnownSpan (Right allT) False em

    -- eix :: Eix a  is implicit
    data Derivation a
        -- ∀ t ∈ tspan  .  lookup t eix = deriveEgo t seenOcc contDerivation
        = KnownSpan
            { derTspan   :: Either Time SpanExc
            , derSeenOcc :: Bool
            , derContDerivation :: EventM a
            }
        -- | ???

-- Now a natural fist attempt at a solution is obvious: start with an initial
-- knowledge base and continue evaluating derivations until all terminate or
-- deadlock:

    solution1 :: Inputs -> KnowledgeBase
    solution1 inputs = go initialKb
        where
        initialFacts = concat
            [ SomeEventFact eix <$> eventFacts
            | InputEl eix (Left eventFacts) <- inputs
            ]
        initialDerivations =
            [ SomeDerivation eix (startDerivationForAllTime eventM)
            | InputEl eix (Right eventM) <- inputs
            ]
        initialKb = KnowledgeBase initialFacts initialDerivations

        go :: KnowledgeBase -> KnowledgeBase
        go kb = let (kb', hasChanged) = stepDerivations kb
                in if hasChanged
                        then go kb'
                        else kb'

        -- Tries to step all derivations once.
        stepDerivations
            :: KnowledgeBase
            -- ^ Current knowledge base.
            -> (KnowledgeBase, Bool)
            -- ^ (New knowledge base, True is the new knowledge base is different from the old).
        stepDerivations (KnowledgeBase facts derivations)
            = (KnowledgeBase kb'facts kb'derivations, anyChanged)
            where
            (kb'facts, kb'derivations, anyChanged) = foldl'
                (\(facts', derivations', changed)
                  someDerivation@(SomeDerivation eix derivation)
                  -> case stepDerivation facts' derivation of
                    Nothing ->
                        ( facts'
                        , someDerivation:derivations'
                        , changed
                        )
                    Just (newFacts, newDerivations) ->
                        ( (SomeEventFact eix <$> newFacts) ++ facts'
                        , (SomeDerivation eix <$> newDerivations) ++ derivations'
                        , True
                        )
                )
                (facts, [], False)
                derivations

        -- This is the important part that should correspond to the `deriveE`
        -- denotation.
        stepDerivation
            :: [SomeEventFact]       -- ^ Current facts. Used to query for existing facts
            -> Derivation a     -- ^ Derivation to step
            -> Maybe ([EventFact a], [Derivation a])
                                -- ^ Nothing if no progress. Else Just the new facts and new derivations.
        stepDerivation facts derivation = case derivation of
            KnownSpan tspan seenOcc contDerivation -> case contDerivation of
                Pure a -> Just $ case (seenOcc, tspan) of
                            (True, Left t) -> ([FactMayOcc t (Just a)], [])
                            -- TODO looks like an invariant that `seenOcc -> tspan is a point in time (i.e. not a span)`
                            (True, Right _) -> error "stepDerivation: encountered non-instantaneous event occurrence."
                            (False, Left t) -> ([FactMayOcc t Nothing], [])
                            (False, Right tspanSpan) -> ([FactNoOcc tspanSpan], [])
                NoOcc -> Just $ case tspan of
                            Left t          -> ([FactMayOcc t Nothing], [])
                            Right tspanSpan -> ([FactNoOcc tspanSpan], [])
                GetE  eixb mayOccToCont -> case spanLookupEFacts tspan eixb facts of
                    ([], _) -> Nothing
                    (factsB, unknowns) -> Just $ (
                        -- For knowns, split and try to progress the derivation.
                        mconcat
                            [ case factB of
                                FactNoOcc subTspan -> let
                                    newCont = mayOccToCont Nothing
                                    newDer  = KnownSpan (Right subTspan) seenOcc newCont
                                    in fromMaybe
                                        ([], [newDer])
                                        -- ^ Couldn't progress further: no new facts, but we've progressed the derivation up to newDer.
                                        (stepDerivation facts newDer)
                                        -- ^ Try to progress further.
                                FactMayOcc t maybeOccB -> case maybeOccB of
                                    -- This is simmilar to above
                                    Nothing -> let
                                        newCont = mayOccToCont Nothing
                                        newDer  = KnownSpan (Left t) seenOcc newCont
                                        in fromMaybe
                                            ([], [newDer])
                                            (stepDerivation facts newDer)
                                    Just b -> let
                                        newCont = mayOccToCont (Just b)
                                        newDer  = KnownSpan (Left t) True newCont
                                        in fromMaybe
                                            ([], [newDer])
                                            (stepDerivation facts newDer)
                            | factB <- factsB
                            ]
                        <>
                        -- For unknowns, simply split the derivation into the
                        -- unknown subspans.
                        ([], [KnownSpan subTspan seenOcc contDerivation | subTspan <- unknowns])
                        )
                PrevE eixb mayPrevToCont -> _ -- This is where shit gets real!


    -- | Directly look up all known facts for a given event and time or time
    -- span.
    spanLookupEFacts
        :: Either Time SpanExc
        -- ^ Time or span to lookup
        -> EIx a
        -- ^ Event to lookup
        -> [SomeEventFact]
        -- ^ All known facts.
        -> ([EventFact a], [Either t SpanExc])
        -- ^ ( Facts about the given event
        --   , unknown times and time spans )
        --   The union of these facts and times and time spans should exactly
        --   equal the input time/time span.
    spanLookupEFacts = _





{-
{-
# NFRP Implementation and Semantics

NFRP is a networked FRP system. We start by looking only at "Events"

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
point in time an event is occurring either exactly once or not at all. We can now
answer the question of "is an event occurring at a given time?":
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
        deriving newtype Eq

    data SomeEventFact = forall a . SomeEventFact (EIx a) (EventFact a)

    data KnowledgeBase = KnowledgeBase [SomeEventFact]

    newKnowledgeBase :: KnowledgeBase
    newKnowledgeBase = KnowledgeBase []

    factsE :: EIx a -> KnowledgeBase -> [EventFact a]
    factsE (EIx eix) (KnowledgeBase es)
        = [ unsafeCoerce fact
            | SomeEventFact (EIx eix') fact <- es
            , eix == eix'
            ]
{-
That represents the current knowledge of a set of events (and later also
behaviors). As we receive new facts, we can add them to the `KnowledgeBase`:

    insertFact :: SomeEventFact -> KnowledgeBase -> KnowledgeBase
    insertFact = ...

This isn't as simple as appending facts as we also want to derive knowledge from
existing facts. How exactly we derive all this knowledge is a main source of
complexity when implementing NFRP.

# Semantics of (Partial) Event

Throughout the implementation of NFRP we always think of events as partial i.e.
we only have knowledge of events for explicit periods of time. We make partial
knowledge explicit with the following denotation:

    ⟦ Event a ⟧ = [EventFact a]   -- Where facts' time spans never overlap

    data SpanExc = ...
-}
    data EventFact a
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

    isOccurring :: Time -> EIx a -> KnowledgeBase -> Maybe Bool
    isOccurring time eix kb = fmap isJust (lookupE time eix kb)

    toFactSpan :: EventFact a -> FactSpan
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
total number of events we want to describe. In the context of a video games, we
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
        | ReturnOcc a
        | ReturnNoOcc
        -- These are explained in the next section.
        -- | forall b . LatestE   (EIx b) (Maybe b -> EventM a)
        | forall b . PreviousE (EIx b) (Maybe b -> EventM a)

    deriving instance Functor EventM

    -- | Required this event to be occurring in order for the resulting event to
    -- be occur.
    requireE :: EIx a -> EventM a
    requireE eix = GetE eix (maybe ReturnNoOcc ReturnOcc)

    -- | Optionally require this event. In order for the resulting event to
    -- occur, at least 1 of all `getE`ed events must be occurring.
    getE :: EIx a -> EventM (MaybeOcc a)
    getE eix = GetE eix (maybe (ReturnOcc Nothing) (ReturnOcc . Just))

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

{- APPENDIX -}

    -- TODO

    instance Applicative EventM where
    instance Monad EventM where
-}
