module Experiment.CarrierRefuse where

    {-
type HoledF = Product RawExprF Maybe
type Holed = Fix HoledF

skipHolesF :: (RawExprF a -> a) -> (HoledF a -> a)
skipHolesF alg (Pair fa _) = alg fa

dehole :: Holed -> Expr
dehole = cata $ skipHolesF embed

replace :: Expr -> String -> Expr -> Expr
replace = undefined

eval :: Expr -> Holed
eval = cata f
    where
    f :: RawExprF Holed -> Holed
    f holedF = Fix $ Pair holedF (handle holedF)
    handle :: RawExprF Holed -> Maybe Holed
    handle (LitF _) = Nothing
    handle (AbsF _ _ _) = Nothing
    handle (VarF env name) = eval <$> get env name -- Explicit recursion? In my recursion schemes?
    handle (IfF cond true false) =
        case dehole cond of -- Replace w/ do-notation
          Fix (LitF (Bool True))  -> Just true -- It's more common than you'd think
          Fix (LitF (Bool False)) -> Just false --(NOTE: Fix o Bifix or Mutrec would solve this explicit second recursion)
          _                       -> Nothing
    handle (LetF name arg body) = undefined
    handle (AppF func args) = undefined
    handle (PrimOpF prim) = undefined
    -}
