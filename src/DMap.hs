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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module DMap where

import Data.Coerce
import Data.Kind
import Data.Map (Map)
import qualified Data.Map as M
import GHC.Exts (Any)
import Unsafe.Coerce

-- | A dependant map
newtype DMap (ix :: Type -> Type) (v :: Type -> Type)
    = DMap (Map (SomeIx ix) (v Any))
        -- ^ Map. Key must be coerced and values must be unsafeCoerced.

instance Semigroup (v Any) => Semigroup (DMap ix v) where
  (DMap a) <> (DMap b) = DMap $ M.unionWith (<>) a b

data SomeIx ix = forall a . Coercible (ix a) Int => SomeIx (ix a)
instance Eq (SomeIx ix) where
  (SomeIx ixA) == (SomeIx ixB)
    = coerce ixA == (coerce ixB :: Int)
instance Ord (SomeIx ix) where
  compare (SomeIx ixA) (SomeIx ixB)
    = compare (coerce ixA) (coerce ixB :: Int)

data El ix v = forall a . Coercible (ix a) Int => El (ix a) (v a)

fromList :: [El ix v] -> DMap ix v
fromList els = DMap $ M.fromList
    [ ( SomeIx ix
      , unsafeCoerceVA v
      )
    | El ix v <- els
    ]

fromListWith :: (forall a . v a -> v a -> v a) -> [El ix v] -> DMap ix v
fromListWith f els = DMap $ M.fromListWith f
    [ ( SomeIx ix
      , unsafeCoerceVA v
      )
    | El ix v <- els
    ]

empty :: DMap ix v
empty = DMap M.empty

singleton :: Coercible (ix a) Int => ix a -> v a -> DMap ix v
singleton ix = DMap . M.singleton (SomeIx ix) . unsafeCoerceVA

lookup :: Coercible (ix a) Int => ix a -> DMap ix v -> Maybe (v a)
lookup ix (DMap m)
    = (unsafeCoerce :: Maybe (v Any) -> Maybe (v a))
    $ M.lookup (SomeIx ix) m

(!) :: Coercible (ix a) Int
    => DMap ix v
    -> ix a
    -> v a
(!) (DMap m) ix
    = (unsafeCoerce :: v Any -> v a)
    $ m M.! (SomeIx ix)

keys :: DMap ix v -> [SomeIx ix]
keys (DMap m) = M.keys m

unsafeCoerceVA :: v a -> v Any
unsafeCoerceVA = unsafeCoerce