{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wincomplete-uni-patterns #-}

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module KnowledgeBase.DMap where

import Data.Coerce
import Unsafe.Coerce
import Data.Kind
import qualified Data.Map as Map
import Data.Map (Map)

newtype DMap (ix :: Type -> Type) (v :: Type -> Type) = DMap (Map Int ())
alter :: Coercible (ix a) Int
    => (Maybe (v a) -> Maybe (v a))
    -> ix a
    -> DMap ix v
    -> DMap ix v
alter f ix (DMap m)
    = DMap $ Map.alter
        ((unsafeCoerce :: Maybe (v a) -> Maybe ())
            . f
            . (unsafeCoerce :: Maybe () -> Maybe (v a)))
        (coerce ix)
        m

lookup :: Coercible (ix a) Int
    => ix a
    -> DMap ix v
    -> Maybe (v a)
lookup ix (DMap m) = unsafeCoerce $ Map.lookup (coerce ix) m

(!) :: Coercible (ix a) Int
    => DMap ix v
    -> ix a
    -> v a
(!) (DMap m) ix = unsafeCoerce (m Map.! coerce ix)