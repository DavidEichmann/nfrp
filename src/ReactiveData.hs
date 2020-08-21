{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module ReactiveData
    -- ( -- Language Definition
    --   Tag (..)
    -- , FieldType (..)
    -- , KeyB
    -- , KeyE
    -- , KeySE
    -- , FieldIx (..)
    -- , V, SE, E

    -- , Rule
    -- , sourceEventDef
    -- , foldB
    -- , behavior
    -- , event
    -- , getB
    -- , getNextB
    -- , getE

    -- -- Knowledge base management
    -- , KnowledgeBase
    -- , newKnowledgeBase
    -- , insertFacts
    -- , lookupB
    -- , lookupE

    -- -- Facts
    -- , Fact
    -- , facts
    -- , factNoChangeSpanE
    -- )
    where


import Data.Kind
import Generics.SOP
import Generics.SOP.NP
import Generics.SOP.Universe

import qualified TheoryFast as TF
import           TheoryFast (KnowledgeBase, EIx(..))

--
-- FRP surface language (This shouled be moved to FRP module)
--

-- | Initialize a new KnowledgeBase from the given game definition.
mkKnowledgeBase :: FieldIx game => game 'Definition -> KnowledgeBase
mkKnowledgeBase gameDef = TF.mkKnowledgeBase $ traverseFields gameDef
    (\eix (Field SourceEventDef) -> TF.InputEl eix (Left []))
    (\eix (Field (EventDef)) -> TF.InputEl eix (Right todo))
    (\(VIx eix) (Field (ValueDef)) -> TF.InputEl eix (Left todo))
    where
      todo = error "TODO implement mkKnowledgeBase"

      -- I need a way to insert the initial value of a value field. I need to
      -- extend InputEl / Theory some how so that I can start with some facts,
      -- then have all other time spans be derived so we have:
      --   InputEl (EIx a) [Fact a] (Maybe (ValueM a))
      -- Only a Maybe incase we want to leave that undefined (useful in e.g. tests)

data SourceEventDef a   = SourceEventDef
sourceEventDef :: Field game 'SourceEvent 'Definition a
sourceEventDef = Field SourceEventDef
data EventDef (game :: Tag -> Type) a = EventDef -- [FactE a] (Rule game (Maybe a))
data ValueDef (game :: Tag -> Type) a = ValueDef -- [FactB a] (Rule game a)


--
-- IX Stuff
--

data FieldType
    = SourceEvent
    | Event
    | Value

data Tag
    = Raw
    | Index
    | Definition

newtype Field game fieldType gameData a = Field { unF :: F game fieldType gameData a }

type family F (game :: Tag -> Type) (fieldType :: FieldType) (gameData :: Tag) a :: Type where

    F _ 'SourceEvent 'Raw a = Maybe a
    F _ 'Event       'Raw a = Maybe a
    F _ 'Value       'Raw a = a

    F _ 'SourceEvent 'Index a = EIx a
    F _ 'Event       'Index a = EIx a
    F _ 'Value       'Index a = VIx a

    F _    'SourceEvent 'Definition a = SourceEventDef a
    F game 'Event       'Definition a = EventDef game a
    F game 'Value       'Definition a = ValueDef game a

type V  game f a = Field game 'Value       f a
type E  game f a = Field game 'Event       f a
type SE game f a = Field game 'SourceEvent f a

newtype VIx a = VIx (EIx a) deriving (Eq, Ord, Show)
-- data Ix a = Ix_B (VIx a) | Ix_E (EIx a)

eIx :: (F game eventType 'Index a ~ EIx a, FieldIx game)
    => (game 'Index -> Field game eventType 'Index a)
    -> EIx a
eIx k = unF (k fieldIxs)

bIx :: FieldIx game => KeyB game a -> VIx a
bIx k = unF (k fieldIxs)

type KeyB  game (a :: Type) = forall (gameData :: Tag) . game gameData -> Field game 'Value       gameData a
type KeyE  game (a :: Type) = forall (gameData :: Tag) . game gameData -> Field game 'Event       gameData a
type KeySE game (a :: Type) = forall (gameData :: Tag) . game gameData -> Field game 'SourceEvent gameData a
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
        :: game gameData
        -> (forall x . EIx x -> Field game 'SourceEvent gameData x -> a)
        -> (forall x . EIx x -> Field game 'Event       gameData x -> a)
        -> (forall x . VIx x -> Field game 'Value       gameData x -> a)
        -> [a]
    default traverseFields :: forall gameData xs a . (IsProductType (game gameData) xs, All (IsGameField game gameData) xs)
        => game gameData
        -> (forall x . EIx x -> Field game 'SourceEvent gameData x -> a)
        -> (forall x . EIx x -> Field game 'Event       gameData x -> a)
        -> (forall x . VIx x -> Field game 'Value       gameData x -> a)
        -> [a]
    traverseFields game fse fe fb =
      hcollapse $
      hczipWith
        (Proxy @(IsGameField game gameData))
        (mapKIK (\ ix -> dispatch ix fse fe fb))
        index_NP
        (productTypeFrom game)

--
-- Generic FieldIx
--

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

class IsGameField game gameData a where
  dispatch ::
       Int
    -> (forall x . EIx x -> Field game 'SourceEvent gameData x -> b)
    -> (forall x . EIx x -> Field game 'Event       gameData x -> b)
    -> (forall x . VIx x -> Field game 'Value       gameData x -> b)
    -> a
    -> b

instance IsGameField game gameData (Field game 'SourceEvent gameData a) where
  dispatch ix fse _fe _fb field = fse (EIx ix) field

instance IsGameField game gameData (Field game 'Event       gameData a) where
  dispatch ix _fse fe _fb field = fe  (EIx ix) field

instance IsGameField game gameData (Field game 'Value       gameData a) where
  dispatch ix _fse _fe fb field = fb  (VIx (EIx ix)) field