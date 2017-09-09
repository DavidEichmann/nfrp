 {-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Module to actuate a circuit description
module Circuit.Actuate
  ( ) where

import Control.Monad
import Data.IORef
import Data.Kind
import Data.Proxy

import Circuit.Description

actuate ::
  Proxy (owner :: node)
  -> Inputs node owner
  -> IO (RefBehavior node output)
  -> Handler output
actuate ownerProxy inputs outputHandler = undefined

{-
type Handler a = a -> IO ()

type AddHandler a = Handler a -> IO ()

-- c -> current node
-- o -> owner node
-- a -> value type
type family LocalInput (node :: nodes) (owner :: nodes) a where
  LocalInput owner owner a = AddHandler a
  LocalInput _ owner a = ()

data PNEvent (ins :: nodes -> *) (outs :: nodes -> *) a
  = forall (owner :: nodes) (node :: nodes). LocalE (Proxy owner)
                                                   (ins node -> AddHandler a)
  | forall b. LiftE (b -> a) (PNEvent ins outs b)
  | MergeE (a -> a -> a) (PNBehavior ins outs a) (PNBehavior ins outs a)

-- PNBehavior inputAddHandlerCollection behavoirCollection ValueType
-- This is a description of a networked behavior
data PNBehavior (ins :: nodes -> *) (outs :: nodes -> *) a
  = forall b. LiftB1 (b -> a)
                    (NBehavior ins outs b)
  | forall b c. LiftB2 (b -> c -> a)
                      (NBehavior ins outs b)
                      (NBehavior ins outs c)

newtype NBehavior (ins :: nodes -> *) (outs :: nodes -> *) a =
  NBehavior (IORef (PNBehavior ins outs a))

nBeh :: PNBehavior ins outs a -> IO (NBehavior ins outs a)
nBeh pnbeh = NBehavior <$> newIORef pnbeh

lift1 :: (a -> b) -> NBehavior ins outs a -> IO (NBehavior ins outs b)
lift1 f ba = nBeh $ LiftB1 f ba

lift2 ::
     (a -> b -> c)
  -> NBehavior ins outs a
  -> NBehavior ins outs b
  -> IO (NBehavior ins outs c)
lift2 f ba bb = nBeh $ LiftB2 f ba bb

data Behavior' =
  forall a. Behavior' (Behavior a)

newtype Behavior a =
  Behavior (Node a)

newtype BehaviorSink a =
  BehaviorSink (Node a)

data BehaviorSinkUpdate a =
  BehaviorSinkUpdate (BehaviorSink a)
                     a

data BehaviorSinkUpdate' =
  forall a. BehaviorSinkUpdate' (BehaviorSinkUpdate a)

data Node a =
  Node (IORef a) -- ^ value.
       (IORef Bool) -- ^ is valid.
       (IO a) -- ^ calculate the value.
       [Behavior'] -- ^ parent behaviors.
       [Behavior'] -- ^ child behaviors.
       (IORef [a -> IO ()]) -- ^ listeners.

data Node' =
  forall a. Node' (Node a)

addHandler :: Node a -> Handler a -> IO ()
addHandler (Node _ _ _ _ _ lsR) handler = modifyIORef' lsR (handler :)

fromLocalInput ::
     forall (node :: nodes) (owner :: nodes) a (ins :: nodes -> *) (outs :: nodes -> *).
     (ins node -> AddHandler a)
  -> IO (NBehavior ins outs a)
fromLocalInput addH = nBeh (Local (Proxy @owner) addH)

getBeh :: Node a -> IO a
getBeh (Node valueR isValidR calc _ _ _) = do
  isValid <- readIORef isValidR
  if isValid
    then readIORef valueR
    else do
      newValue <- calc
      writeIORef valueR newValue
      writeIORef isValidR True
      return newValue

-- Invalidate the node and its children.
-- returns newly invalidated nodes that have listeners
invalidate :: Node' -> IO [Node']
invalidate node@(Node' (Node _ isValidR _ _ cs lsR)) = do
  isValid <- readIORef isValidR
  if not isValid
    then return []
    else do
      writeIORef isValidR False
      ls <- readIORef lsR
      childInvalidations <-
        concat <$>
        mapM (invalidate . (\(Behavior' (Behavior node)) -> Node' node)) cs
      return $
        if null ls
          then childInvalidations
          else node : childInvalidations

transaction :: [BehaviorSinkUpdate'] -> IO ()
transaction updates
  -- Invalidate recursivelly with early termination. Keep track of nodes with listeners.
 = do
  observedNodes <-
    concat <$>
    forM
      updates
      (\(BehaviorSinkUpdate' (BehaviorSinkUpdate behaviorSink newValue)) ->
         setBeh behaviorSink newValue)
  -- Update nodes with listeners and fire all listeners.
  -- TODO without events an explicite update is not needed
  forM_ observedNodes $ \(Node' node@(Node _ _ _ _ _ lsR)) -> do
    ls <- readIORef lsR
    val <- getBeh node
    forM_ ls (\l -> l val)

-- Returns newly invalidated nodes.
setBeh :: BehaviorSink a -> a -> IO [Node']
setBeh (BehaviorSink node) newValue = do
  let (Node valueR _ _ _ _ _) = node
  observedNodesCurrent <- invalidate (Node' node)
  writeIORef valueR newValue
  return observedNodesCurrent
-}
