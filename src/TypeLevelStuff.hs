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

module TypeLevelStuff (IsElem, AllC, Sing(..), Sings(..)) where

import Data.Proxy
import Data.Kind
import GHC.TypeLits

class Sing t where
    type SingT t
    sing :: Proxy t -> SingT t

type family Head xs where Head (x:xs) = x

class Sing (Head ts) => Sings ts where
    sings :: Proxy ts -> [SingT (Head ts)]
instance forall t . Sing t => Sings '[t] where
    sings _ = [sing (Proxy @t)]
instance forall t tt ts
    . ( Sing t
      , Sings (tt:ts)
      , SingT t ~ SingT (Head (tt:ts))
    ) => Sings (t:tt:ts) where
    sings _ = sing (Proxy @t) : sings (Proxy @(tt:ts))

-- class Sings k () where
--     type SingsT a
--     sings :: Proxy a -> [SingsT a]
-- instance Sing k t => Sings '[t] where
--     type SingsT '[t] = SingT k t
--     sings _ = [sing (Proxy @t)]
-- instance Sings (t:tt:ts) where
--     type SingsT (t:tt:ts) = SingT (tt:ts)
--     sings _ = sing (Proxy @t) : sings (Proxy @(tt:ts))

-- TODO implement if needed.
-- type family IsSubsetEq (as :: [k]) (bs :: [k]) :: Constraint where

-- Type level list elem function
type family IsElem (a :: k) (b :: [k]) :: Constraint where
    IsElem a as = IsElem' a as as

-- Helper that keeps the original list so that an error message can be created.
type family IsElem' (a :: k) (b :: [k]) (orig :: [k]) :: Constraint where
    IsElem' a (a:_) _      = True ~ True
    IsElem' a (_:as) orig  = IsElem' a as orig
    IsElem' a _ orig       = TypeError (ShowType a
                                       :<>: Text " not an element of "
                                       :<>: ShowType orig)

-- All constraint
type family AllC (cFn :: k -> Constraint) (xs :: [k]) :: Constraint where
    AllC f '[]     = ()
    AllC f (e:es) = (f e, AllC f es)