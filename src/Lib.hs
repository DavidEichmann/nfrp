{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Lib
  ( module ReExport
  ) where

import Circuit.Actuate as ReExport
import Circuit.Description as ReExport

f a = a + 1
