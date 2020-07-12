{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

import qualified GHC.Generics as GHC
import Control.Monad (when)
import Data.Kind (Type)
import Data.Maybe (catMaybes, isJust, isNothing, fromMaybe)

-- import NFRP
-- import FRP
import Time (Time)
import TimeSpan
import Theory (VIx(..))
import Theory as T
import TheoryFast as TF
-- import KnowledgeBase
-- import KnowledgeBase.Timeline
import System.Environment
import Synthetic

main :: IO ()
main = do
    nStr:imp:_ <- getArgs
    let (vixs, ts, ins) = syntheticN (read nStr)
        lookupV = case imp of
            "t"  -> let kb =  T.solution1 ins in \t vix -> T.lookupVKB t vix kb
            "tf" -> let kb = TF.solution1 ins in \t vix ->TF.lookupVKB t vix kb
    print $ sum
        [ case lookupV t vix of
            Known x -> x
            Unknown -> 0
        | vix <- vixs
        , t <- ts
        ]
