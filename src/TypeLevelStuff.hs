{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module TypeLevelStuff (IsElem, AllC, Sing(..), Sings(..), ElemT(..)) where

import Data.Proxy
import Data.Typeable
import Data.Kind
import GHC.TypeLits

class Sing t where
    type SingT t :: Type
    sing :: Proxy t -> SingT t

class Sings ts t where
    sings :: Proxy ts -> [t]
instance Sings '[] t where
    sings _ = []
instance (Sing x, SingT x ~ t, Sings xs t) => Sings (x:xs) t where
    sings _ = sing (Proxy @x) : sings (Proxy @ xs)

-- Type level list elem function
type family IsElem (a :: k) (b :: [k]) :: Constraint where
    IsElem a as = IsElem' a as as

-- Helper that keeps the original list so that an error message can be created.
type family IsElem' (a :: k) (b :: [k]) (orig :: [k]) :: Constraint where
    IsElem' a (a:_) _      = ()
    IsElem' a (_:as) orig  = IsElem' a as orig
    IsElem' a _ orig       = TypeError (ShowType a
                                       :<>: Text " not an element of "
                                       :<>: ShowType orig)

-- All constraint
type family AllC (cFn :: k -> Constraint) (xs :: [k]) :: Constraint where
    AllC f '[]     = ()
    AllC f (e:es) = (f e, AllC f es)

class ElemT k (xs :: [k]) where
    elemT :: forall (e :: k) . Typeable e => Proxy e -> Proxy xs -> Bool
instance ElemT k '[] where
    elemT _ _ = False
instance (Typeable x, ElemT k xs)
         => ElemT k (x : xs) where
    elemT (_ :: Proxy e) _ = case eqT @e @x of
        Just Refl -> True
        Nothing   -> elemT (Proxy @e) (Proxy @xs)