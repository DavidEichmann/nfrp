{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

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
        myLookupV = case imp of
            "t"  -> let kb =  T.mkKnowledgeBase ins in \t eix -> T.lookupVKB t eix kb
            "tf" -> let kb = TF.mkKnowledgeBase ins in \t eix ->TF.lookupVKB t eix kb
    print $ sum
        [ case myLookupV t eix of
            Known (Occ x) -> x
            _ -> 0
        | eix <- vixs
        , t <- ts
        ]
