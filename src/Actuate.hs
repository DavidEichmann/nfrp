{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecursiveDo #-}
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

module NFRP
    (
    -- Framework
    -- , SourceEvent
    -- , EventInjector
    -- , newSourceEvent
    -- , injectEvent
    -- , actuate
    ) where

import Safe
import Control.Monad.State
import Unsafe.Coerce
import Data.IORef
import Data.Kind
import Data.Dynamic
import Data.Maybe (mapMaybe)
import qualified Data.List as List
import Data.List (find, sortBy)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Function (on)
import qualified Data.Graph as Graph
import qualified Data.Map as Map

import Control.Concurrent
import Control.Concurrent.Async

import Debug.Trace
import Control.Exception.Base (assert)

import TypeLevelStuff
