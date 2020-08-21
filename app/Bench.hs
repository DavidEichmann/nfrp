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
import Theory (EIx(..))
import Theory as T
import TheoryFast as TF
-- import KnowledgeBase
-- import KnowledgeBase.Timeline
import System.Environment
import Synthetic

main :: IO ()
main = do
    nEStr:nTStr:imp:_ <- getArgs
    let (vixs, ts, ins) = syntheticN (read nEStr) (read nTStr)
        lookupV = case imp of
            "t"  -> let kb =  T.solution1 ins in \t eix -> T.lookupVKB t eix kb
            "tf" -> let kb = TF.solution1 ins in \t eix ->TF.lookupVKB t eix kb
    print $ sum
        [ case lookupV t eix of
            Known (Occ x) -> x
            _ -> 0
        | eix <- vixs
        , t <- ts
        ]
