{-# LANGUAGE TemplateHaskell, RecordWildCards #-}
module GHC.Examples where

import GHC.Expr
import GHC.Classes
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

plus =
    let primOpName = Name (OccName "+") NameS
        primOpContract = [Integer, Integer]
        primOpFunc = \[IntegerL i, IntegerL j] -> IntegerL $ i + j
    in
    (primOpName, FP (-1) NoRedex $ PrimOp {..})

times =
    let primOpName = Name (OccName "*") NameS
        primOpContract = [Integer, Integer]
        primOpFunc = \[IntegerL i, IntegerL j] -> IntegerL $ i * j
    in
    (primOpName, FP (-1) NoRedex $ PrimOp {..})

liftCommendDefinePrims raw = foldr define (commend raw) [plus, times]

ex1 = liftCommendDefinePrims $(liftEx [| 2 * (1 + 3 * 5) |])
ex2 = liftCommendDefinePrims $(liftEx [| 2 * (1 + (3) * 5) |])

repl :: ExpG Redex -> IO ()
repl expr = do
    print $ ppr $ condemn expr
    let ids = collect expr
    case ids of
        [] -> pure ()
        ids@(defaultId:_) -> do
            print ids
            idRaw <- getLine
            case reads idRaw of
                []         -> repl $ hatchAll $ eat defaultId expr
                (id, ""):_ -> repl $ hatchAll $ eat id expr
                _          -> repl expr
