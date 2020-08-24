{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module ReactiveData
    ( -- Language Definition
      Tag (..)
    , FieldType (..)
    , FieldIx (..)
    , Field (..)
    , Occ (ReactiveData.Occ, NoOcc)
    , foldOccs
    , ValueDef (..)
    , EventDef (..)
    , SourceEventDef (..)
    , V, E, SE
    , Time
    , value
    , event
    , sourceEvent
    , getE
    , prevV

    -- Knowledge base management
    , KnowledgeBase
    , mkKnowledgeBase
    , progressKB
    , getLatestPerField
    )
    where


import           Control.Monad.Fail (MonadFail)
import           Data.Coerce (coerce)
import           Data.Foldable (Foldable(foldl'))
import           Data.Kind
import           Generics.SOP
import           Generics.SOP.NP
import           Generics.SOP.Universe

import           Time
import           TimeSpan
import           Theory (Fact(..), SomeValueFact(..))
import qualified TheoryFast as TF
import           TheoryFast (KnowledgeBase, EIx(..))
import Data.Maybe (fromJust)

--
-- TODO
--
-- * It would be nice to get rid of the Field newtype.
-- * Can we get rid of type family F? Maybe use GADTs instead?
--

--
-- FRP surface language (This shouled be moved to FRP module)
--

foldOccs :: Foldable f => (a -> a -> a) -> f (Occ t a) -> Occ t a
foldOccs f = foldl'
    (\a b -> case a of
        NoOcc -> b
        Occ a' -> case b of
            NoOcc -> a
            Occ b' -> Occ (f a' b')
    )
    NoOcc

-- | Initialize a new KnowledgeBase from the given game definition.
mkKnowledgeBase :: FieldIx game => game 'Definition -> KnowledgeBase
mkKnowledgeBase gameDef = TF.mkKnowledgeBase $ traverseFields gameDef
    (\eix (Field SourceEventDef) -> TF.InputEl eix [noOcc0] Nothing)
    (\eix (Field (EventDef def)) -> TF.InputEl eix [noOcc0] (Just (eventMToValueM def)))
    (\(VIx eix) (Field (ValueDef val0 def)) -> TF.InputEl eix [noOcc0, Fact_Occ ["Static initial value"] 0 val0] (Just (eventMToValueM def)))
    where
    noOcc0 = Fact_NoOcc ["NoOcc at t<=0"] (DS_SpanExc (spanExc Nothing (Just 0)))

-- Time based progression. Implies no source event occurrences between start and
-- end time (exclusive), and inserts source events wherever they occur in the
-- given input.
progressKB :: forall game . FieldIx game => Time -> Time -> game 'SourceEvents -> KnowledgeBase -> KnowledgeBase
progressKB timeA timeB es kb = TF.insertFacts
  ( TF.listToFacts $ concat $ traverseFields es
      (\eix (Field xMay) -> SomeValueFact eix <$>
          [ noOccFactSpan
          , case xMay of
              Nothing -> noOccFactPoint
              Just x -> Fact_Occ [] timeB x])
      -- Events and Values are derived automatically.
      (\_ (Field ()) -> [])
      (\_ (Field ()) -> [])
  )
  kb
  where
  noOccFactSpan :: Fact a
  noOccFactSpan = Fact_NoOcc [] (TF.DS_SpanExc (spanExc (Just timeA) (Just timeB)))

  noOccFactPoint :: Fact a
  noOccFactPoint = Fact_NoOcc [] (TF.DS_Point timeB)

-- | Get all latest known values.
getLatestPerField :: FieldIx game => proxy game -> Time -> KnowledgeBase -> game 'Values
getLatestPerField _ t kb
  = mapFields
      -- TF.lookupLatestKnownKB t eix kb
      (\(Field _) -> Field ())
      (\(Field _) -> Field ())
      (\(Field (VIx vix)) -> Field (fromJust $ TF.lookupLatestKnownKB t vix kb))
  $ fieldIxs

data ValueDef (game :: Tag -> Type) a = ValueDef a (forall t . EventM game t (Occ t a))

value :: a -> (forall t . EventM game t (Occ t a)) -> Field game 'Value 'Definition a
value a0 def = Field $ ValueDef a0 def

data EventDef (game :: Tag -> Type) a = EventDef (forall t . EventM game t (Occ t a))

event :: (forall t . EventM game t (Occ t a)) -> Field game 'Event 'Definition a
event def = Field $ EventDef def

data SourceEventDef a = SourceEventDef

sourceEvent :: Field game 'SourceEvent 'Definition a
sourceEvent = Field SourceEventDef

eventMToValueM :: EventM (game :: Tag -> Type) t (Occ t a) -> TF.ValueM a
eventMToValueM (EventM em) = do
  occA <- em
  case occA of
    Occ a -> TF.Pure (TF.Occ a)
    NoOcc -> TF.Pure TF.NoOcc

newtype EventM (game :: Tag -> Type) t a = EventM (TF.ValueM a)
  deriving newtype (Functor, Applicative, Monad, MonadFail)

data Occ t a
  = SomeEventIsOccurring t => Occ a
  | NoOcc

coerceOcc :: Occ (KnownOccTime t) a -> Occ t a
coerceOcc = coerce
type role SomeEventIsOccurring phantom

deriving stock instance Functor (Occ t)

class SomeEventIsOccurring (t :: Type)
data KnownOccTime t
instance SomeEventIsOccurring (KnownOccTime t)

unsafeOcc :: a -> Occ t a
unsafeOcc = coerceOcc . Occ

getE :: forall game t a eventish
  . (F game eventish 'Index a ~ EIx a, FieldIx game)
  => (game 'Index -> Field game eventish 'Index a)
  -> EventM game t (Occ t a)
getE eixF = EventM $ do
  eOcc <- TF.getE (eIx (unF . eixF))
  return $ case eOcc of
    TF.Occ a -> unsafeOcc a
    TF.NoOcc -> NoOcc

prevV :: forall game t a . (FieldIx game, SomeEventIsOccurring t) => (game 'Index -> Field game 'Value 'Index a) -> EventM game t a
prevV vixF = EventM $ do
  let VIx eix = vIx (unF . vixF)
  vMay <- TF.prevV eix
  case vMay of
    Nothing -> error "Value doesn't have an initial value. Are we trying to sample it before it was created?"
    Just v -> return v


--     TF.NoOcc -> NoOcc


--
-- IX Stuff
--

data FieldType
    = SourceEvent
    | Event
    | Value

data Tag
    = Id
    | Index
    | Definition
    | SourceEvents
    | Values

newtype Field game fieldType tag a = Field { unF :: F game fieldType tag a }

type family Field_Game field where
  Field_Game (Field game fieldType tag a) = game

type family Field_FieldType field where
  Field_FieldType (Field game fieldType tag a) = fieldType

type family Field_Tag field where
  Field_Tag (Field game fieldType tag a) = tag

type family Field_Value field where
  Field_Value (Field game fieldType tag a) = a

type family F (game :: Tag -> Type) (fieldType :: FieldType) (tag :: Tag) a :: Type where

    F _ 'SourceEvent 'Id a = Maybe a
    F _ 'Event       'Id a = Maybe a
    F _ 'Value       'Id a = a

    F _ 'SourceEvent 'Index a = EIx a
    F _ 'Event       'Index a = EIx a
    F _ 'Value       'Index a = VIx a

    F _    'SourceEvent 'Definition a = SourceEventDef a
    F game 'Event       'Definition a = EventDef game a
    F game 'Value       'Definition a = ValueDef game a

    F _    'SourceEvent 'SourceEvents a = Maybe a
    F game 'Event       'SourceEvents a = ()
    F game 'Value       'SourceEvents a = ()

    F _    'SourceEvent 'Values a = ()
    F game 'Event       'Values a = ()
    F game 'Value       'Values a = a

type V  game f a = Field game 'Value       f a
type E  game f a = Field game 'Event       f a
type SE game f a = Field game 'SourceEvent f a

newtype VIx a = VIx (EIx a) deriving (Eq, Ord, Show)
-- data Ix a = Ix_B (VIx a) | Ix_E (EIx a)

eIx :: FieldIx game => (game 'Index -> EIx a) -> EIx a
eIx k = k fieldIxs

vIx :: FieldIx game => (game 'Index -> VIx a) -> VIx a
vIx k = k fieldIxs

-- data Key game (a :: Type)
--     = KeyB (KeyB game a)
--     | KeyE (KeyE game a)

class FieldIx (game :: Tag -> *) where
    fieldIxs :: game 'Index
    default fieldIxs :: (IsProductType (game 'Index) xs, All IsField xs) => game 'Index
    fieldIxs =
      productTypeTo $
      hcmap
        (Proxy @IsField)
        (mapKI fieldIx)
        index_NP

    traverseFields
        :: game tag
        -> (forall x . EIx x -> Field game 'SourceEvent tag x -> a)
        -> (forall x . EIx x -> Field game 'Event       tag x -> a)
        -> (forall x . VIx x -> Field game 'Value       tag x -> a)
        -> [a]
    default traverseFields :: forall tag xs a
        . ( IsProductType (game tag) xs
          , All (IsGameField game tag) xs
          )
        => game tag
        -> (forall x . EIx x -> Field game 'SourceEvent tag x -> a)
        -> (forall x . EIx x -> Field game 'Event       tag x -> a)
        -> (forall x . VIx x -> Field game 'Value       tag x -> a)
        -> [a]
    traverseFields game fse fe fb =
      hcollapse $
      hczipWith
        (Proxy @(IsGameField game tag))
        (mapKIK (\ ix -> dispatch ix fse fe fb))
        index_NP
        (productTypeFrom game)

    mapFields
        :: (forall x . Field game 'SourceEvent tagA x -> Field game 'SourceEvent tagB x)
        -> (forall x . Field game 'Event       tagA x -> Field game 'Event       tagB x)
        -> (forall x . Field game 'Value       tagA x -> Field game 'Value       tagB x)
        -> game tagA
        -> game tagB
    default mapFields :: forall tagA tagB xsA xsB
        . ( MapFields game tagA tagB xsA xsB
          , IsProductType (game tagA) xsA
          , IsProductType (game tagB) xsB
          )
        => (forall x . Field game 'SourceEvent tagA x -> Field game 'SourceEvent tagB x)
        -> (forall x . Field game 'Event       tagA x -> Field game 'Event       tagB x)
        -> (forall x . Field game 'Value       tagA x -> Field game 'Value       tagB x)
        -> game tagA
        -> game tagB
    mapFields fse fe fv gA
      = productTypeTo
      $ mapFields' fse fe fv
      $ productTypeFrom gA

--
-- Generic FieldIx
--

class MapFields (game :: Tag -> Type) (tagA :: Tag) (tagB :: Tag) (xsA :: [Type]) (xsB :: [Type]) where
  mapFields'
    :: (forall x . Field game 'SourceEvent tagA x -> Field game 'SourceEvent tagB x)
    -> (forall x . Field game 'Event       tagA x -> Field game 'Event       tagB x)
    -> (forall x . Field game 'Value       tagA x -> Field game 'Value       tagB x)
    -> NP I xsA
    -> NP I xsB

instance MapFields game tagA tagB '[] '[] where
  mapFields' _ _ _ _ = Nil

instance MapFields game tagA tagB xsA xsB => MapFields game tagA tagB (Field game 'SourceEvent tagA a ': xsA) (Field game 'SourceEvent tagB a ': xsB) where
  mapFields' fse fe fv (I xa :* xsA) = I (fse xa) :* mapFields' fse fe fv xsA

instance MapFields game tagA tagB xsA xsB => MapFields game tagA tagB (Field game 'Event tagA a ': xsA) (Field game 'Event tagB a ': xsB) where
  mapFields' fse fe fv (I xa :* xsA) = I (fe xa) :* mapFields' fse fe fv xsA

instance MapFields game tagA tagB xsA xsB => MapFields game tagA tagB (Field game 'Value tagA a ': xsA) (Field game 'Value tagB a ': xsB) where
  mapFields' fse fe fv (I xa :* xsA) = I (fv xa) :* mapFields' fse fe fv xsA

-- instance MapFields game (Field game 'SourceEvent tag a) where
--   mapFields' fse _ _ = fse

-- instance MapFields game (Field game 'Event tag a) where
--   mapFields' _ fe _ = fe

-- instance MapFields game (Field game 'Value tag a) where
--   mapFields' _ _ fv = fv

index_NP :: SListI xs => NP (K Int) xs
index_NP =
  ana_NP (\ (K i) -> (K i, K (i + 1))) (K 0)

class IsField a where
  fieldIx :: Int -> a

instance IsField (Field game 'SourceEvent 'Index a) where
  fieldIx ix = Field $ EIx ix

instance IsField (Field game 'Event 'Index a) where
  fieldIx ix = Field $ EIx ix

instance IsField (Field game 'Value 'Index a) where
  fieldIx ix = Field $ VIx (EIx ix)

class IsGameField game tag a where
  dispatch ::
       Int
    -> (forall x . EIx x -> Field game 'SourceEvent tag x -> b)
    -> (forall x . EIx x -> Field game 'Event       tag x -> b)
    -> (forall x . VIx x -> Field game 'Value       tag x -> b)
    -> a
    -> b

instance IsGameField game tag (Field game 'SourceEvent tag a) where
  dispatch ix fse _fe _fb field = fse (EIx ix) field

instance IsGameField game tag (Field game 'Event       tag a) where
  dispatch ix _fse fe _fb field = fe  (EIx ix) field

instance IsGameField game tag (Field game 'Value       tag a) where
  dispatch ix _fse _fe fb field = fb  (VIx (EIx ix)) field