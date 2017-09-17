{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Lib
  ( module ReExport
  ) where

import Circuit.Actuate as ReExport

f a = a + 1
