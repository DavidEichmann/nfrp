{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}

module Theory
  ( module Theory
  , TimeSpan(..)
  ) where

  import qualified Control.Monad as M
  import Data.Hashable
  import Data.Kind
  import Data.List (find, foldl')
  import Data.Maybe (fromMaybe, listToMaybe, mapMaybe)
  import Data.String
  import Data.Text.Prettyprint.Doc
  import Unsafe.Coerce


  import Time
  import TimeSpan

  type DerivationTraceEl a = String
  type DerivationTrace a = [DerivationTraceEl a]
  appendDerTrace :: DerivationTrace a -> DerivationTraceEl a -> DerivationTrace a
  appendDerTrace = flip (:)

  data VFact a
    = VFact_NoOcc (DerivationTrace a) TimeSpan
    | VFact_Occ   (DerivationTrace a) Time    a

  data Fact a
    = Fact_VFact (VFact a)
    | Fact_DerivationClearance (DerivationTrace a)
        [SomeEIx] -- PrevV Dependencies during the clearance time span
        SpanExc   -- Clearance time span
    -- ^ This is generally used just internally and not used in `InputEl`.
    -- This corresponds to a Derivation with non-zero span jurisdiction that is
    -- is saturated (final value is calculated i.e. cont = Pure _).

  factTSpan :: VFact a -> TimeSpan
  factTSpan (VFact_NoOcc _ tspan) = tspan
  factTSpan (VFact_Occ _ t _) = DS_Point t

  factTrace :: VFact a -> DerivationTrace a
  factTrace (VFact_NoOcc tr _) = tr
  factTrace (VFact_Occ tr _ _) = tr

-- We have some set of `EIx`s, 𝔼, and a definition for each: either a source
-- event or derived event. We want to calculate all facts about the derived
-- events from the source events.

  data InputEl = forall a . InputEl
      (EIx a)
      -- ^ The event this corresponds to
      [VFact a]
      -- ^ All (initial) known facts. This is used e.g. to set the initial value
      -- of Value (i.e. Behavior) events.
      (Maybe (ValueM a))
      -- ^ Derivation for time spans not in the (initial) known facts.
  type Inputs = [InputEl]

  inputsToInitialFactsAndDerivations :: Inputs -> ([SomeFact], [SomeDerivation])
  inputsToInitialFactsAndDerivations inputs = (initialFacts, initialDerivations)
    where
    initialFacts = concat
      [ SomeFact eix . Fact_VFact <$> eventFacts
      | InputEl eix eventFacts _ <- inputs
      ]
    initialDerivations =
      [ SomeDerivation eix (mkDerivationForTimeSpan ts eventM)
      | InputEl eix initFacts (Just eventM) <- inputs
      , ts <- (allT :: TimeSpan) `difference` (factTSpan <$> initFacts)
      ]

  newtype MaybeOcc a = MaybeOcc { maybeOccToMaybe :: Maybe a }
    deriving newtype (Eq, Ord, Show, Read, Functor, Applicative, Monad)
  pattern Occ :: a -> MaybeOcc a
  pattern Occ a = MaybeOcc (Just a)
  pattern NoOcc :: MaybeOcc a
  pattern NoOcc = MaybeOcc Nothing
  {-# COMPLETE Occ, NoOcc #-}

  newtype EIx (a :: Type) = EIx { unEIx :: Int}     -- Index of an event
    deriving newtype (Eq, Ord, Hashable)

  instance Show (EIx a) where
    show (EIx a) = "EIx " ++ show a

  data SomeEIx = forall a . SomeEIx (EIx a)

  instance Eq SomeEIx where (SomeEIx (EIx a)) == (SomeEIx (EIx b)) = a == b
  instance Ord SomeEIx where compare (SomeEIx (EIx a)) (SomeEIx (EIx b)) = compare a b
  instance Show SomeEIx where show (SomeEIx eix) = show eix
  instance Hashable SomeEIx where
    hash (SomeEIx a) = hash a
    hashWithSalt i (SomeEIx a) = hashWithSalt i a

-- Derived events are expressed with the ValueM monad:

  data ValueM a
    -- | Return an occurence. Must be NoOcc if no GetE has returned a Occ yet.
    -- TODO enforce this in the API e.g. by only allowing construction from an
    -- witnessed event... or Occ contains a constraint "proof" that an event is
    -- witnessed
    = Pure (MaybeOcc a)
    -- | Get current event value if occurring.
    | forall b . GetE  (EIx b)
                       (MaybeOcc b -> ValueM a)
    -- | Get previous event's value strictly before current time. You may only
    -- use this if:
    --  1. There is no (transitive) self dependency via `PrevE`.
    --  2. OR An event was observed via `GetE`. This ensures that the jurisdiction
    --     is a point and hence we can depend on facts from before this point.
    --  3. OR
    --
    -- NOTE: I previously allowed a (transitive) self dependency via PrevV, but
    -- this creates a deadlock:
    --
    --        a = do
    --          aPrevVal <- fromMaybe 0 <$> prevV a
    --          e <- getE incE
    --          return $ case e of
    --            NoOcc -> NoOcc
    --            Occ () -> return (aPrevVal + 1)
    --
    -- The problem is that the derivation is immediately stuck waiting on a self
    -- reference which will never produce Facts. This is no longer an issue as
    | forall b . PrevV (EIx b)
                       (Maybe b -> ValueM a)

  deriving instance Functor ValueM

  instance Applicative ValueM where
    (<*>) = M.ap
    pure = return

  instance Monad ValueM where
    return = Pure . Occ
    fa >>= fmb = case fa of
      Pure (Occ a) -> fmb a
      Pure NoOcc -> Pure NoOcc
      GetE  eixb cont -> GetE  eixb ((>>= fmb) . cont)
      PrevV eixb mayPrevToCont -> PrevV eixb ((>>= fmb) . mayPrevToCont)

  instance MonadFail ValueM where
    fail _ = Pure NoOcc

  getE :: EIx a -> ValueM (MaybeOcc a)
  getE eix = GetE eix (Pure . Occ)

  requireE :: EIx a -> ValueM a
  requireE eix = GetE eix Pure

  -- | Note that this returns Nothing if there is no previous event
  prevV :: EIx a -> ValueM (Maybe a)
  prevV eix = PrevV eix (Pure . Occ)

  -- | Note that this returns Nothing if there is no current/previous event
  -- WARNING: this uses getE which may witness an event. Higher level APIs would
  -- abstract this away. Other wise the user may get an event occurrence without
  -- expecting it because the similar prevV function never witnesses events.
  currV :: EIx a -> ValueM (Maybe a)
  currV eix = do
    currMay <- getE eix
    case currMay of
      Occ a -> return (Just a)
      NoOcc -> prevV eix

  onEvent :: EIx a -> (a -> ValueM b) -> ValueM (MaybeOcc b)
  onEvent eix withA = do
    mayE <- getE eix
    case mayE of
      NoOcc -> return NoOcc
      Occ a -> Occ <$> withA a

-- Give some `inputs :: Inputs`, we have this denotation for an event/ValueM:

  -- lookupV :: Time -> EIx a -> MaybeOcc a
  -- lookupV t eix = case lookupInputs eix inputs of
  --   Left lookupSourceE -> lookupSourceE t
  --   Right eventM -> deriveE t eventM

  -- deriveE ::  Time -> ValueM a -> MaybeOcc a
  -- deriveE t eventM = deriveEgo False t eventM

  -- deriveEgo :: Bool -> Time -> ValueM a -> MaybeOcc a
  -- deriveEgo seenE t (Pure a) = if seenE then Occ a else error "Invalid event definition"
  -- deriveEgo seenE t (GetE eixB cont) = deriveEgo t (\bMay -> cont (seenE || isJust bMay) (lookupV t eixB) bMay)
  -- deriveEgo seenE t (PrevV eixB cont)
  --   = case max t'  where  t' < t
  --        ∧  isJust (lookupV t' exiB)
  --     then deriveEgo t (cont (lookupV t' exiB))
  --     else deriveEgo t (cont Nothing)

  newtype MaybeKnown a = MaybeKnown { maybeKnownToMaybe :: Maybe a }
    deriving newtype (Eq, Ord, Show, Read, Functor, Applicative, Monad)
  pattern Known :: a -> MaybeKnown a
  pattern Known a = MaybeKnown (Just a)
  pattern Unknown :: MaybeKnown a
  pattern Unknown = MaybeKnown Nothing
  {-# COMPLETE Known, Unknown #-}

  lookupVKB :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (MaybeOcc a)
  lookupVKB t eix (KnowledgeBase facts _) = lookupV t eix facts

  lookupVKBTrace :: Time -> EIx a -> KnowledgeBase -> MaybeKnown (DerivationTrace a)
  lookupVKBTrace t eix (KnowledgeBase facts _) = lookupVTrace t eix facts

  lookupV :: Time -> EIx a -> [SomeFact] -> MaybeKnown (MaybeOcc a)
  lookupV t eix facts = fmap
    (\case
      VFact_NoOcc _ _   -> NoOcc
      VFact_Occ   _ _ v -> Occ v
    )
    (lookupVFact t eix facts)

  lookupVTrace :: Time -> EIx a -> [SomeFact] -> MaybeKnown (DerivationTrace a)
  lookupVTrace t eix facts = factTrace <$> lookupVFact t eix facts

  lookupVFact :: Time -> EIx a -> [SomeFact] -> MaybeKnown (VFact a)
  lookupVFact t eix facts = MaybeKnown $ listToMaybe $
    filter ((`intersects` t) . factTSpan) (factsV' eix facts)

-- We store a knowledge base:

  data SomeFact = forall a . SomeFact (EIx a) (Fact a)
  data SomeVFact = forall a . SomeVFact (EIx a) (VFact a)
  data SomeDerivation = forall a . SomeDerivation (EIx a) (Derivation a)

  data KnowledgeBase = KnowledgeBase [SomeFact] [SomeDerivation]

  factsV :: EIx a -> KnowledgeBase -> [VFact a]
  factsV eix (KnowledgeBase es _)
    = factsV' eix es

  factsV' :: EIx a -> [SomeFact] -> [VFact a]
  factsV' (EIx eix) es
    = [ (unsafeCoerce :: VFact a' -> VFact a) fact
      | SomeFact (EIx eix') (Fact_VFact fact) <- es
      , eix == eix'
      ]

-- A derivation is a partial evaluation of the `deriveE` function, universally
-- quantified over a range of time.

  mkDerivationForAllTime :: ValueM a -> Derivation a
  mkDerivationForAllTime = mkDerivationForTimeSpan (DS_SpanExc allT)

  mkDerivationForTimeSpan :: TimeSpan -> ValueM a -> Derivation a
  mkDerivationForTimeSpan ts em = Derivation [] ts em False

  -- eix :: Eix a  is implicit
  data Derivation a
    -- When `derPrevTspan /= []` we solve in strictly chronological order.
    --
    -- ∀ t ∈ ttspan   (t <= min_{p ∈ derPrevDeps} {firstChangeTime(p, ttspan)}   when derPrevDeps /= [])
    --     . lookup t eix = deriveEgo t contDerivation
    = Derivation
      { derTrace :: DerivationTrace a
      , derTtspan :: TimeSpan
      -- ^ Time span/point of jurisdiction.
      , derContDerivation :: ValueM a
      , derSeenOcc :: Bool
      -- ^ Have we seen an occurence yet (can only be true if TTspan is a point)
      }

    -- -- | DS_SpanExc tspan ⟹ t ∈ tspan
    -- DS_SpanExcInc SpanExcInc

    -- -- | DS_SpanExcIncFirstOcc lo  ⟹ t ∈ tspan
    -- forall a . DS_SpanExcIncFirstOcc SpanExc (EIx a)

-- Now a natural fist attempt at a solution is obvious: start with an initial
-- knowledge base and continue evaluating derivations until all terminate or
-- deadlock:

  mkKnowledgeBase :: Inputs -> KnowledgeBase
  mkKnowledgeBase inputs = iterateUntilChange initialKb
    where
    (initialFacts, initialDerivations) = inputsToInitialFactsAndDerivations inputs
    initialKb = KnowledgeBase initialFacts initialDerivations

    iterateUntilChange :: KnowledgeBase -> KnowledgeBase
    iterateUntilChange kb = let (kb', hasChanged) = stepDerivations kb
        in if hasChanged
            then iterateUntilChange kb'
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
          -> case stepDerivation eix derivations facts' derivation of
          Nothing ->
            ( facts'
            , someDerivation:derivations'
            , changed
            )
          Just (newFacts, newDerivations) ->
            ( (SomeFact eix <$> newFacts) ++ facts'
            , (SomeDerivation eix <$> newDerivations) ++ derivations'
            , True
            )
        )
        (facts, [], False)
        derivations

    -- This is the important part that should correspond to the `deriveE`
    -- denotation.
    stepDerivation
      :: forall a
      .  EIx a
      -- ^ Event index that the derivation corresponds to.
      -> [SomeDerivation]
      -- ^ Current derivations. Used to detect PrevV deadlock.
      -> [SomeFact]
      -- ^ Current facts. Used to query for existing facts
      -> Derivation a
      -- ^ Derivation to step
      -> Maybe ([Fact a], [Derivation a])
      -- ^ Nothing if no progress. Else Just the new facts and new derivations.
    stepDerivation eix allDerivations facts derivation = case derivation of
      Derivation dtrace ttspan contDerivation seenOcc -> case contDerivation of
        Pure NoOcc -> let
          dtrace' = appendDerTrace dtrace $
            "Pure NoOcc (t=" ++ show ttspan ++ ")."
          in Just ([Fact_VFact $ VFact_NoOcc dtrace' ttspan], [])
        Pure (Occ a) -> case ttspan of
          DS_SpanExc _ -> error "Pure (Occ _) when jurisdiction is not a point"
          DS_Point t -> let
                  dtrace' = appendDerTrace dtrace $
                    "Jurisdiction is a point (t=" ++ show t ++ "), ValueM is `Pure a`."
                  in Just ([Fact_VFact $ VFact_Occ dtrace' t a], [])
        GetE eixb cont -> case spanLookupVFacts ttspan eixb facts of
            ([], _) -> Nothing
            (factsB, unknowns) -> Just $ (
                -- For knowns, split and try to progress the derivation.
                mconcat
                  [ case factB of
                    VFact_NoOcc _ subTspan -> let
                      newCont = cont NoOcc
                      newDer  = Derivation dtrace subTspan newCont seenOcc
                                  `withDerTrace`
                                  ("Split on GetE dep (" ++ show eixb ++ ") VFact_NoOcc")
                      in fromMaybe
                        -- Couldn't progress further: no new facts, but we've progressed the derivation up to newDer.
                        ([], [newDer])
                        -- Try to progress further.
                        (stepDerivation eix allDerivations facts newDer)
                    VFact_Occ _ t valB -> let
                        newCont = cont (Occ valB)
                        newDer  = Derivation dtrace (DS_Point t) newCont True
                                  `withDerTrace`
                                  ("Split on GetE dep (" ++ show eixb ++ ") VFact_Occ")
                        in fromMaybe
                          ([], [newDer])
                          (stepDerivation eix allDerivations facts newDer)
                  | factB <- factsB
                  ]
                <>
                -- For unknowns, simply split the derivation into the
                -- unknown subspans.
                ( []
                , [ Derivation dtrace subTspan contDerivation seenOcc
                    `withDerTrace`
                    ("Split on GetE dep (" ++ show eixb ++ ") unknown point or span.")
                  | subTspan <- unknowns
                  ]
                )
              )

        PrevV eixB mayPrevToCont -> case ttspan of
          DS_Point t -> case lookupPrevV t eixB facts of
            Unknown -> Nothing
            Known prevBMay -> Just $ let
              newCont = mayPrevToCont prevBMay
              newDer  = Derivation dtrace ttspan newCont seenOcc
                    `withDerTrace`
                    ("Use known PrevV value of dep (" ++ show eixB ++ ")")
              in fromMaybe
                ([], [newDer])
                (stepDerivation eix allDerivations facts newDer)

          -- !! The Plan
          -- !! Try and split on facts about eixB.
          DS_SpanExc _ -> let
            (knownSpansAndValueMays, unknownSpans) = spanLookupPrevV ttspan eixB facts
            in if null knownSpansAndValueMays
              then Nothing
              else Just $ (
                -- For knowns, split and try to progress the derivation.
                mconcat
                  [ let
                    newCont = mayPrevToCont prevVMay
                    newDer  = Derivation dtrace ttspan' newCont seenOcc
                        `withDerTrace`
                          ("Split on known facts")
                    in fromMaybe
                      -- Couldn't progress further: no new facts, but we've progressed the derivation up to newDer.
                      ([], [newDer])
                      -- Try to progress further.
                      (stepDerivation eix allDerivations facts newDer)
                  | (ttspan', prevVMay) <- knownSpansAndValueMays
                  ]
                <>
                -- For unknowns, simply split the derivation into the
                -- unknown subspans.
                ([], [Derivation dtrace subTspan contDerivation seenOcc
                        `withDerTrace`
                          ("Split on unknown span or point")
                      | subTspan <- unknownSpans])
                )

  -- | Directly look up the previous value that satisfies the predicate
  -- (strictly before the given time).
  lookupPrevV
    :: Time
    -- ^ Time t
    -> EIx a
    -- ^ Event to lookup.
    -> [SomeFact]
    -- ^ Known facts.
    -> MaybeKnown (Maybe a)
    -- ^ Unknown: if unknown
    -- Known Nothing: if no value satisfying the predicate occurs strictly before t.
    -- Known (Just a): the latest (projected) value satisfying the predicate (strictly before time t).
  lookupPrevV t eix allFacts = MaybeKnown . listToMaybe $ mapMaybe
        (\case
          VFact_NoOcc _ (DS_SpanExc tspan)
            -- The fact spans just before time t
            | tspan `contains` t || Just t == spanExcJustAfter tspan
            -> case spanExcJustBefore tspan of
                  Nothing -> Just Nothing
                  Just tLo -> maybeKnownToMaybe $ lookupCurrV tLo eix allFacts
            | otherwise -> Nothing
          VFact_NoOcc _ (DS_Point _) -> Nothing
          VFact_Occ _ _ _ -> Nothing
        )
        (factsV' eix allFacts)


    -- factSpanExcs = mapMaybe factSpa
    --     (\case
    --       VFact_Occ _ _ _ -> Nothing
    --       VFact_NoOcc _ tspan _ -> Just tspan
    --     )
    --     (factsV' eix allFacts)
    -- -- We must find a VFact_Occ just before or containing t.
    -- tspanMay = find
    --     (\tspan -> tspan `contains` t || Just t == spanExcJustAfter tspan)
    --     factSpanExcs
    -- in case tspanMay of
    --   Nothing -> Unknown
    --   Just tspan -> case spanExcJustBefore tspan of
    --     Nothing -> Known Nothing
    --     Just t' -> lookupCurrV t' eix allFacts

  -- | Directly look up the current (i.e. latest) event occurrence (equal or before the given time).
  lookupCurrV
    :: Time
    -- ^ Time t
    -> EIx a
    -- ^ Event to lookup.
    -> [SomeFact]
    -- ^ Known facts.
    -> MaybeKnown (Maybe a)
    -- ^ Unknown: if unknown
    -- Known Nothing: if no value satisfying the predicate occurs at or before t.
    -- Known (Just a): the latest occ value (at or before t).
  lookupCurrV t eix allFacts = let
    factMay = find (\f -> factTSpan f `contains` t) (factsV' eix allFacts)
    in case factMay of
      Nothing -> Unknown
      Just fact -> case fact of
        VFact_NoOcc _ (DS_SpanExc tspan) -> case spanExcJustBefore tspan of
            Nothing -> Known Nothing
            Just t' -> lookupCurrV t' eix allFacts
        VFact_NoOcc _ (DS_Point _) -> lookupPrevV t eix allFacts
        VFact_Occ _ _ a -> Known (Just a)


  -- | Directly lookup the previous value for an event over a span of time.
  spanLookupPrevV
    :: TimeSpan
    -- ^ Time or span to lookup
    -> EIx a
    -- ^ Event to lookup
    -> [SomeFact]
    -- ^ All known facts.
    -> ([(TimeSpan, Maybe a)], [TimeSpan])
    -- ^ ( Known values about the given EIx
    --   , unknown times and time spans )
    --   The union of these times and time spans should exactly
    --   equal the input time/time span.
  spanLookupPrevV tspan eix allFacts = let
    facts = prevVFacts eix allFacts
    knownFacts =
        [ (ttspan', aMay)
        | (factTspan, aMay) <- facts
        , Just ttspan' <- [factTspan `intersect` tspan]
        ]
    knownTSpans = fst <$> knownFacts
    unknownTSpans = tspan `difference` knownTSpans
    in (knownFacts, unknownTSpans)


  -- | Get all known PervV spans for an event
  prevVFacts
    :: forall a
    .  EIx a
    -- ^ Event to lookup
    -> [SomeFact]
    -- ^ All known facts.
    -> [(TimeSpan, Maybe a)]
    -- ^ All known previous event values (if one exists)
  prevVFacts eix allFacts = concat
    [ case fact of
      VFact_NoOcc _ (DS_SpanExc tspan) -> let
        mayPrevVMay :: MaybeKnown (Maybe a)
        mayPrevVMay = case spanExcJustBefore tspan of
          -- Span starts at -∞ so that's a known Nothing previous event
          Nothing -> Known Nothing
          -- Span starts at a time prevT
          Just prevT -> lookupCurrV prevT eix allFacts
        in case mayPrevVMay of
            Unknown -> []
            Known prevVMay -> (DS_SpanExc tspan, prevVMay) : [(DS_Point nextT, prevVMay) | Just nextT <- [spanExcJustAfter tspan]]

      -- Point knowledge is handled by the above case
      VFact_NoOcc _ (DS_Point _) -> []
      VFact_Occ _ _ _ -> []

    | fact <- factsV' eix allFacts
    ]

  -- | Directly look up all known facts for a given EIx and time or time
  -- span.
  spanLookupVFacts
    :: TimeSpan
    -- ^ Time or span to lookup
    -> EIx a
    -- ^ Event to lookup
    -> [SomeFact]
    -- ^ All known facts.
    -> ([VFact a], [TimeSpan])
    -- ^ ( Facts about the given EIx
    --   , unknown times and time spans )
    --   The union of these facts and times and time spans should exactly
    --   equal the input time/time span.
  spanLookupVFacts tspan eix allFacts = let
    facts = factsV' eix allFacts
    knownFacts =
        [ case (fact, ttspan') of
          (VFact_NoOcc dtrace _, DS_SpanExc tspan') -> VFact_NoOcc dtrace (DS_SpanExc tspan')
          (VFact_NoOcc dtrace _, DS_Point   t'    ) -> VFact_NoOcc dtrace (DS_Point t')
          (VFact_Occ _ _ _   , DS_SpanExc _) -> error "Intersection between SpanExc and Time must be Just Time or Nothing"
          (VFact_Occ dtrace _ occMay, DS_Point t') -> VFact_Occ dtrace t' occMay
        | fact <- facts
        , Just ttspan' <- [factTSpan fact `intersect` tspan]
        ]
    knownTSpans = factTSpan <$> knownFacts
    unknownTSpans = tspan `difference` knownTSpans
    in (knownFacts, unknownTSpans)



{- APPENDIX -}

  -- TODO

  withDerTrace
    :: Derivation a
    -- ^ Derivation (without a trace entry for the latest step) trace
    -> String
    -- ^ Msg describing most recent step taken in derivation.
    -> Derivation a
    -- ^ Derivation with added traced entry.
  withDerTrace (Derivation oldTrace ttspan cont seenOcc) msg
    = Derivation (oldTrace `appendDerTrace` dMsg) ttspan cont seenOcc
    where
    dMsg = "Derivation "
          ++ showTtspan ttspan ++ " "
          ++ "cont=" ++ showPeakValueM cont
          ++ ": " ++ msg

    showTtspan (DS_Point t) = "t=" ++ show t
    showTtspan (DS_SpanExc tspan) = "t∈" ++ show tspan

    showPeakValueM :: ValueM a -> String
    showPeakValueM (Pure _) = "Pure{}"
    showPeakValueM (GetE ix _) = "(GetE " ++ show ix ++ " _)"
    showPeakValueM (PrevV ix _) = "(PrevV " ++ show ix ++ " _)"



  instance Pretty (EIx a) where
    pretty = fromString . show

  instance Pretty SomeEIx where
    pretty (SomeEIx eix) = pretty eix

  instance Pretty (Derivation a) where
    pretty Derivation{..} = nest 2 $ vsep
        [ "Derivation"
        , "derTrace = " <> "_" -- pretty derTrace
        , "derTtspan = " <> pretty derTtspan
        , "derContDerivation = " <> "_" -- pretty derContDerivation
        , "derSeenOcc = " <> pretty derSeenOcc
        ]

  instance Pretty KnowledgeBase where
    pretty _kb = "KnowledgeBase _"
