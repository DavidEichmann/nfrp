{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module TypeLevelStuff (IsElem) where

import Data.Kind
import GHC.TypeLits

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