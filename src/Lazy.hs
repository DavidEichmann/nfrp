{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
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

-- | An example in ghci:
--      > aL <- atomically $ lazy (return "hello")
--      > bL <- atomically $ lazy (return "world")
--      > cL <- atomically $ lazy $ do { a <- get aL; b <- get bL; return (a ++ " " ++ b); }
--      > atomically $ tryEvaluateLazy cL
--      Just "hello world"

module Lazy where

import Control.Concurrent.STM
import Control.Exception
import Data.Either (isRight)
import Data.Maybe (isJust)

-- | A lazy value.
data Lazy a = Lazy
    { lazyValue :: TMVar a
    -- ^ The value (iff evaluated).
    , lazyEval :: STM (Either (STM Bool) a)
    -- Try to evaluate the value, else return a (STM Bool) which is a quick
    -- check that returns False if it is *not* worth reevaluating.
    -- This does not set lazyValue nor lazyCanReEval.
    , lazyCanReEval :: TMVar (STM Bool)
    -- The latest check from lazyEval if one exists.
    }


data MultipleEmptyLazySets = MultipleEmptyLazySets
instance Show MultipleEmptyLazySets where
    show MultipleEmptyLazySets = "Tried to set a lazy value multiple times."
instance Exception MultipleEmptyLazySets

emptyLazy :: forall a . STM (Lazy a, a -> STM ())
emptyLazy = do
    valTMVar <- newEmptyTMVar
    fireTMVar <- newEmptyTMVar
    lazyCanReEvalTMVar <- newEmptyTMVar
    let la = Lazy
            { lazyValue     = valTMVar
            , lazyEval      = maybe (Left (return True)) Right
                                 <$> tryReadTMVar fireTMVar
            , lazyCanReEval = lazyCanReEvalTMVar
            }
    return
        ( la
        , \ a -> do
            laHasValue <- isEvaluated la
            if laHasValue
                then throwSTM MultipleEmptyLazySets
                else putTMVar fireTMVar a
        )

tryEvaluate :: Lazy a -> STM (Maybe a)
tryEvaluate l = either (const Nothing) Just <$> tryEvaluate' l

tryEvaluate' :: Lazy a -> STM (Either (STM Bool) a)
tryEvaluate' (Lazy val eval canReEval) = do
    vMay <- tryReadTMVar val
    case vMay of
        Just v -> return (Right v)
        Nothing -> do
            checkMay <- tryReadTMVar canReEval
            case checkMay of
                Just checkCanReEval -> do
                    canReEvalVal <- checkCanReEval
                    if canReEvalVal
                        then go
                        else return (Left checkCanReEval)
                Nothing -> go
    where
    go = do
        eitherCheckOrVal <- eval
        case eitherCheckOrVal of
            Left checkCanReEval -> do
                putTMVar canReEval checkCanReEval
                return (Left checkCanReEval)
            Right finalVal -> do
                putTMVar val finalVal
                return (Right finalVal)

hasValue :: Lazy a -> STM Bool
hasValue = fmap isRight . tryEvaluate'

isEvaluated :: Lazy a -> STM Bool
isEvaluated l = do
    vMay <- tryReadTMVar (lazyValue l)
    return (isJust vMay)

newtype LazyM a = LazyM { lazy :: STM (Lazy a) }

get :: Lazy a -> LazyM a
get = LazyM . return

instance Functor LazyM where
    fmap f lma = do
        a <- lma
        return (f a)

instance Applicative LazyM where
    pure a = LazyM $ do
        valTMVar <- newTMVar a
        lazyCanReEvalTMVar <- newTMVar (return False)
        return $ Lazy
            { lazyValue     = valTMVar
            , lazyEval      = return (Right a)
            , lazyCanReEval = lazyCanReEvalTMVar
            }
    alm <*> blm = do
        a <- alm
        b <- blm
        return (a b)

instance Monad LazyM where
    return = pure
    (LazyM alm) >>= cont = LazyM $ do
        al <- alm
        valTMVar <- newEmptyTMVar
        lazyCanReEvalTMVar <- newTMVar (return True)
        return Lazy
            { lazyValue     = valTMVar
            , lazyEval
                = do
                    aMay <- tryEvaluate' al
                    case aMay of
                        Left checkReEval -> return (Left checkReEval)
                        Right a -> do
                            bl <- lazy (cont a)
                            tryEvaluate' bl
            , lazyCanReEval = lazyCanReEvalTMVar
            }
