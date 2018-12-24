{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module HMap
    ( HMap
    , (!)
    , insert
    , empty
    ) where

import Data.Typeable
import Data.Dynamic
import Data.Kind
import Data.Map (Map)
import qualified Data.Map as Map

newtype HMap keyKind (value :: keyKind -> Type)
    = HMap (Map TypeRep Dynamic)
    -- ^ map from key's TypeRep to (value key)

(!) :: forall keyKind (key :: keyKind) (value :: keyKind -> Type)
    .  (Typeable key, Typeable value)
    => HMap keyKind value
    -> Proxy key
    -> value key
(HMap dynMap) ! _ = fromDyn
            (dynMap Map.! typeRep (Proxy @key))
            (error "HMap: key donesn't exist")

empty :: HMap a b
empty = HMap Map.empty

insert :: forall keyKind (key :: keyKind) (value :: keyKind -> Type)
    .  (Typeable key, Typeable value)
    => Proxy key
    -> value key
    -> HMap keyKind value
    -> HMap keyKind value
insert kP v (HMap dynMap) = HMap (Map.insert (typeRep kP) (toDyn v) dynMap)