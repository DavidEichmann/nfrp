{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wincomplete-uni-patterns #-}

{-# LANGUAGE Arrows #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | A module for supporting FRP based on a data type. Data can be thought of as
-- a behavior.
module DataFRP where
    -- ( Behaviour
    -- , SourceE

    -- , Definition
    -- , Update
    -- )


-- import Control.Arrow
-- import Control.Concurrent.STM
-- import Control.Exception
-- import Data.Either (isRight)
-- import Data.Maybe (isJust)
-- import Data.Function (fix)
-- import Data.Functor.Identity

-- import Time

-- This should be much simpler. We just have data that changes at certain times
-- we don't allow for delays or anything, we just always specify prev/current time.
-- data changes when events happen

{-

type Event f a = Behaviour f (Occ a)
type family Behaviour f a where
    Behaviour Definition a = a
    Behaviour Update     a = a
    Behaviour Sample     a = a

type family SourceE f a where
    SourceE Definition a = ()
    SourceE Update     a = Occ a
    SourceE Sample     a = Occ a

data SourceEvents
data Definition
data Update
data Sample -- The raw world data at a specific time.
data Active -- Internal rep of an active world

type B a = Behaviour Definition a
type E a = Event Definition a

data Change a = Change | NoChange
-- | Event occurence
data Occ a = NoOcc | Occ a
    deriving stock (Eq, Show, Functor)

--
-- Working example
--

main :: IO ()
main = do
    fireSourceEvents <- actuate gameDef
    fireSourceEvents

fireEvents :: world Active -> world SourceEvents -> world Sample
fireEvents = _


gameDef :: Game Definition
gameDef = fix $ \ game -> Game
    { player1Inputs = ()
    , player2Inputs = ()
    , player1Pos    = inputsToPos (player1Inputs)
    , player2Pos    = (0,0)
    }
    where
    inputsToPos :: E Inputs -> B Pos
    inputsToPos inputs = fold (0,0) $ \oldPos -> do
        input <- get inputs
        let delta = 100
        return $ case input of
            Occ DirLeft  -> Change (-delta,  0)
            Occ DirRight -> Change ( delta,  0)
            Occ DirUp    -> Change ( 0,  delta)
            Occ DirDown  -> Change ( 0, -delta)
            NoOcc        -> NoChange

data Game f = Game
    { player1Inputs :: SourceE f Inputs
    , player2Inputs :: SourceE f Inputs
    , player1Pos    :: Behaviour f Pos
    , player2Pos    :: Behaviour f Pos
    }

data Inputs = DirUp | DirRight | DirDown | DirLeft
    deriving stock (Eq, Ord, Show, Read)

type Pos = (Int, Int)
-}