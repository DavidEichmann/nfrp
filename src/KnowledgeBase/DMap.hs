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
import Data.Maybe (fromMaybe)

-- | A total dependant map
data DMap (ix :: Type -> Type) (v :: Type -> Type)
    = DMap
        (forall a . v a)
        -- ^ Default value
        (Map Int ())
        -- ^ Map. Key must be coerced and values must be unsafeCoerced.

update :: Coercible (ix a) Int
    => (v a -> Maybe (v a))
    -- ^ Nothing means use the default value
    -> ix a
    -> DMap ix v
    -> DMap ix v
update f ix (DMap def m)
    = DMap def $ Map.alter
        ((unsafeCoerce :: Maybe (v a) -> Maybe ())
            . f
            . fromMaybe def
            . (unsafeCoerce :: Maybe () -> Maybe (v a)))
        (coerce ix)
        m

(!) :: Coercible (ix a) Int
    => ix a
    -> DMap ix v
    -> v a
(!) ix (DMap def m)
    = fromMaybe def
    $ (unsafeCoerce :: Maybe () -> Maybe (v a))
    $ Map.lookup (coerce ix) m
