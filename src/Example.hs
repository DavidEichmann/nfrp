{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{-# LANGUAGE PartialTypeSignatures #-}
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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module Example where

import Safe
import Data.Typeable
import NFRP


-- TODO LocalInput and Node types are still hard wired into NFRP but should be moved here.


calculatorCircuit :: Moment ()
calculatorCircuit = do
    aKeyB <- (beh . (Step '0')) =<< (evt $ Source (Proxy @ClientA))
    bKeyB <- (beh . (Step '+')) =<< (evt $ Source (Proxy @ClientB))
    cKeyB <- (beh . (Step '0')) =<< (evt $ Source (Proxy @ClientC))
    
    leftB  <- beh =<< SendB (Proxy @ClientA) (Proxy @'[Server]) <$> readIntB aKeyB
    rightB <- beh =<< SendB (Proxy @ClientC) (Proxy @'[Server]) <$> readIntB cKeyB
    opB    <- beh =<< SendB (Proxy @ClientB) (Proxy @'[Server]) <$> (beh $ MapB (\case
                            '+' -> (+)
                            '/' -> div
                            '*' -> (*)
                            _   -> (-) :: (Int -> Int -> Int)) 
                        bKeyB)

    resultB_ <- beh $ opB `Ap` leftB
    _resultB  <- beh $ resultB_ `Ap` rightB

    return ()

    where
        readIntB :: Typeable o
                 => BehaviorIx o Char -> Moment (BehaviorIx o Int)
        readIntB = beh . MapB (\c -> readDef 0 [c])