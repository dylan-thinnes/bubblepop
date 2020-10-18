{-# LANGUAGE OverloadedStrings #-}
module Bubble.Examples where

import Bubble.Expr

import Data.Fix
import Data.Functor.Product

-- Example
env :: Env
env = set "x" (Fix (Pair (LitF (Int 3)) NoRedex)) empty

primEQ    = AnnR "autoapply" $ PrimOpR $ PrimOp "=" [TInt, TInt] (\[Int i, Int j] -> Bool $ i == j)
primLT    = AnnR "autoapply" $ PrimOpR $ PrimOp "<" [TInt, TInt] (\[Int i, Int j] -> Bool $ i < j)
primTimes = AnnR "autoapply" $ PrimOpR $ PrimOp "*" [TInt, TInt] (\[Int i, Int j] -> Int $ i * j)
primPlus  = AnnR "autoapply" $ PrimOpR $ PrimOp "+" [TInt, TInt] (\[Int i, Int j] -> Int $ i + j)
primMinus = AnnR "autoapply" $ PrimOpR $ PrimOp "-" [TInt, TInt] (\[Int i, Int j] -> Int $ i - j)

primitives :: Env
primitives = foldr (\def@(AnnR _ (PrimOpR (PrimOp name _ _))) env -> set name (refine def primitives) env) empty [primEQ, primLT, primTimes, primPlus, primMinus]

ex_simple :: RawExpr
ex_simple =
    IfR
        (AppR
            primLT
            [ (AppR
                primTimes
                [ VarR "x"
                , LitR (Int 2)
                ])
            , (AppR
                primTimes
                [ LitR (Int 5)
                , LitR (Int 7)
                ])
            ])
        (VarR "x")
        (VarR "y")

ex_simple' = refine ex_simple env

ex_fix :: RawExpr
ex_fix =
    LetR "x" (AppR (VarR "f") [VarR "x"]) (VarR "x")

ex_fix' = refine ex_fix env

ex_lambda :: RawExpr
ex_lambda =
    LetR "plusTwo"
        (AbsR ["y"] (AppR primPlus [LitR (Int 2), (VarR "y")]))
        (AppR primTimes [AppR (VarR "plusTwo") [VarR "x"], LitR (Int 3)])

ex_lambda' = refine ex_lambda env

ex_fac :: RawExpr
ex_fac =
    LetR "fac"
        (AbsR ["i"]
            (IfR
                (AppR primLT
                    [VarR "i"
                    ,LitR (Int 1)
                    ])
                (LitR (Int 1))
                (AppR primTimes
                    [VarR "i"
                    ,AppR (VarR "fac")
                        [AppR primMinus
                            [VarR "i"
                            ,LitR (Int 1)
                            ]]])))
        (AppR (VarR "fac") [LitR (Int 3)])

ex_fac' = refine ex_fac empty

ex_foldr :: RawExpr
ex_foldr =
    LetR "foldr"
        (AbsR ["f", "base", "list"]
            (CaseR (VarR "list")
                [(PCons (Cons ":" [PEscape "head", PEscape "rest"]),
                    AppR (VarR "f") [VarR "head", (AppR (VarR "foldr") [VarR "f", VarR "base", VarR "rest"])])
                ,(PCons (Cons "[]" []),
                    VarR "base")
                ]))
        (AppR (VarR "foldr") [primPlus, LitR (Int 7), EConsR ":" [LitR (Int 2), EConsR ":" [LitR (Int 3), EConsR "[]" []]]])

ex_foldr' = refine ex_foldr empty

ex_deep_case :: RawExpr
ex_deep_case =
    LetR "x"
        (EConsR "Just" [EConsR "Just" [LitR (Int 10)]])
        (CaseR
            (VarR "x")
            [(PCons $ Cons "Just" [PCons $ Cons "Just" [PEscape "y"]], VarR "y")
            ,(PCons $ Cons "Just" [PCons $ Cons "Nothing" []], LitR (Int 2))
            ,(PCons $ Cons "Nothing" [], LitR (Int 1))
            ]
        )

ex_deep_case' = refine ex_deep_case empty

ex_autoapply :: Expr Redex
ex_autoapply = refine expr env
  where
    env = set "foldr" (refine foldr env) empty
    foldr =
        (AnnR "autoapply"
            (AbsR ["f", "base", "list"]
                (AnnR "autorun"
                    (CaseR (VarR "list")
                        [(PCons (Cons ":" [PEscape "head", PEscape "rest"]),
                            AppR (VarR "f") [VarR "head", (AppR (VarR "foldr") [VarR "f", VarR "base", VarR "rest"])])
                        ,(PCons (Cons "[]" []),
                            VarR "base")
                        ]))))
    expr =
        AppR
            (VarR "foldr")
            [ primPlus
            , LitR (Int 7)
            , EConsR ":"
                [ LitR (Int 2)
                , EConsR ":"
                    [ LitR (Int 3)
                    , EConsR "[]" []
                    ]
                ]]
