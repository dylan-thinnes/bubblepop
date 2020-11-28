{-# LANGUAGE OverloadedStrings #-}
module Bubble.Examples where

import Bubble.Expr

import Data.Functor.Foldable hiding (Cons)
import Data.Functor.Product
import Data.Fix (Fix(..))

-- Example
env :: Env
env = set "x" (Fix (Pair (LitF (Int 3)) NoRedex))
    $ set "y" (Fix (Pair (LitF (Int 4)) NoRedex))
    $ set "z" (Fix (Pair (LitF (Int 5)) NoRedex))
    $ empty

primEQ    = AnnR "autoapply" $ PrimOpR $ PrimOp "=" [TInt, TInt] (\[Int i, Int j] -> Bool $ i == j)
primLT    = AnnR "autoapply" $ PrimOpR $ PrimOp "<" [TInt, TInt] (\[Int i, Int j] -> Bool $ i < j)
primTimes = AnnR "autoapply" $ PrimOpR $ PrimOp "*" [TInt, TInt] (\[Int i, Int j] -> Int $ i * j)
primPlus  = AnnR "autoapply" $ PrimOpR $ PrimOp "+" [TInt, TInt] (\[Int i, Int j] -> Int $ i + j)
primMinus = AnnR "autoapply" $ PrimOpR $ PrimOp "-" [TInt, TInt] (\[Int i, Int j] -> Int $ i - j)

primitives :: Env
primitives = foldr (\def@(AnnR _ (PrimOpR (PrimOp name _ _))) env -> set (string name) (refine def primitives) env) empty [primEQ, primLT, primTimes, primPlus, primMinus]

ex_simple :: RawExpr
ex_simple =
    IfR
        ex_operators
        (VarR "x")
        (VarR "y")

ex_simple' = refine ex_simple env

ex_fix :: RawExpr
ex_fix =
    LetR "x" (AppR Prefix (VarR "f") [VarR "x"]) (VarR "x")

ex_fix' = refine ex_fix env

ex_lambda :: RawExpr
ex_lambda =
    LetR "plusTwo"
        (AbsR ["y"] (AppR Infix primPlus [LitR (Int 2), (VarR "y")]))
        (AppR Infix primTimes [AppR Prefix (VarR "plusTwo") [VarR "x"], LitR (Int 3)])

ex_lambda' = refine ex_lambda env

ex_fac :: RawExpr
ex_fac =
    LetR "fac"
        (AbsR ["i"]
            (IfR
                (AppR Infix primLT
                    [VarR "i"
                    ,LitR (Int 1)
                    ])
                (LitR (Int 1))
                (AppR Infix primTimes
                    [VarR "i"
                    ,AppR Prefix (VarR "fac")
                        [AppR Infix primMinus
                            [VarR "i"
                            ,LitR (Int 1)
                            ]]])))
        (AppR Prefix (VarR "fac") [LitR (Int 3)])

ex_fac' = refine ex_fac empty

ex_foldr :: RawExpr
ex_foldr =
    LetR "foldr"
        (AbsR ["f", "base", "list"]
            (CaseR (VarR "list")
                [(PCons (Cons ":" [PEscape "head", PEscape "rest"]),
                    AppR Prefix (VarR "f") [VarR "head", (AppR Prefix (VarR "foldr") [VarR "f", VarR "base", VarR "rest"])])
                ,(PCons (Cons "[]" []),
                    VarR "base")
                ]))
        (AppR Prefix (VarR "foldr") [primPlus, LitR (Int 7), EConsR ":" [LitR (Int 2), EConsR ":" [LitR (Int 3), EConsR "[]" []]]])

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
                            AppR Prefix (VarR "f") [VarR "head", (AppR Prefix (VarR "foldr") [VarR "f", VarR "base", VarR "rest"])])
                        ,(PCons (Cons "[]" []),
                            VarR "base")
                        ]))))
    expr =
        AppR Prefix (VarR "foldr")
            [ primPlus
            , LitR (Int 7)
            , EConsR ":"
                [ LitR (Int 2)
                , EConsR ":"
                    [ LitR (Int 3)
                    , EConsR "[]" []
                    ]
                ]]

ex_operators :: RawExpr
ex_operators =
    AppR
        Infix
        primLT
        [ (AppR
            Infix
            primTimes
            [ VarR "x"
            , (AppR
                Infix
                primPlus
                [ LitR (Int 2)
                , VarR "y"
                ])
            ])
        , (AppR
            Infix
            primPlus
            [ (AppR
                Infix
                primTimes
                [ LitR (Int 2)
                , VarR "z"
                ])
            , LitR (Int 7)
            ])
        ]

ex_operators' = refine ex_operators env

ex_if :: RawExpr
ex_if =
    IfR
        ex_operators
        (VarR "x")
        (VarR "z")

ex_if' = refine ex_if env

ex_let :: RawExpr
ex_let =
    LetR "x" (LitR $ Int 3) $
    LetR "y" (LitR $ Int 4) $
    LetR "z" (LitR $ Int 5) $
    AppR
        Infix
        primLT
        [ (AppR
            Infix
            primTimes
            [ VarR "x"
            , (AppR
                Infix
                primPlus
                [ LitR (Int 2)
                , VarR "y"
                ])
            ])
        , (AppR
            Infix
            primPlus
            [ (AppR
                Infix
                primTimes
                [ LitR (Int 2)
                , VarR "z"
                ])
            , LitR (Int 7)
            ])
        ]

ex_let' = refine ex_let empty

ex_fac_aa :: RawExpr
ex_fac_aa =
    LetR "fac"
        (AnnR "autoapply" $
         AbsR ["i"]
            (IfR
                (AppR Infix primLT
                    [VarR "i"
                    ,LitR (Int 1)
                    ])
                (LitR (Int 1))
                (AppR Infix primTimes
                    [VarR "i"
                    ,AppR Prefix (VarR "fac")
                        [AppR Infix primMinus
                            [VarR "i"
                            ,LitR (Int 1)
                            ]]])))
        (AppR Prefix (VarR "fac") [LitR (Int 3)])

ex_fac_aa' = refine ex_fac_aa empty
