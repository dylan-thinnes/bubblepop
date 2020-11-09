{-# LANGUAGE OverloadedStrings, PatternSynonyms, TemplateHaskell #-}
module Experiment.LambdaCalculusMapping where

import Prelude hiding ((.), (*), succ)
import GHC.Exts (IsString(..))
import Experiment.LambdaCalculusMapping.TH

data Term
  = Lam String Term
  | App Term Term
  | Var String
    deriving (Show)

instance IsString Term where
    fromString = Var

(.) name body = Lam name body
(*) func arg = App func arg

infixl 2 *
infixr 1 .

$(genSingleNames "xyzabcfghn")

s, k, i, fix :: Term
s   = f.g.a. f *a *(g *a)
k   = x.y.   x
i   = x.     x
fix = f.     (x. f *(x *x)) *(x. f *(x *x))

pair :: Term
pair = x.y.f. f *x *y

cons, nil :: Term
cons = x.y.f.g. g *x *(y *f *g)
nil  =     f.g. f

succ, zero :: Term
succ = n.f.x. f *(n *f *x)
zero = f.x.   x

fromN :: Int -> Term
fromN 0 = zero
fromN n = succ *(fromN $ n - 1)
