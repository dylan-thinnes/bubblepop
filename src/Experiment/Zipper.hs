-- Things that should be in Haskell 98 anyways:
{-# LANGUAGE TupleSections #-}
-- Advanced syntactical sugar:
{-# LANGUAGE PatternSynonyms #-}
-- GHC magic:
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
module Experiment.Zipper where

import Data.Void
import Data.Functor.Product
import Data.Functor.Foldable hiding (Cons)
import Control.Monad

import Text.Show.Deriving (deriveShow1)

-- Expression base functor
type Expr = Fix ExprF

data ExprF a
    = AppF a a
    | AbsF String a
    | VarF String
    deriving (Show, Functor, Foldable, Traversable)

deriveShow1 ''ExprF

pattern App e0 e1  = Fix (AppF e0 e1)
pattern Abs name e = Fix (AbsF name e)
pattern Var name   = Fix (VarF name)

-- Crumbs for an Expression Zipper
data Two = Zero | One
    deriving (Show)
data Crumb a
    = AppFC Two a
    | AbsFC String
    -- | VarFC Void
    deriving (Show, Functor)

fillCrumb :: Crumb b -> (a, a) -> (Crumb a, a)
fillCrumb crumb (fill, focus) = (fmap (const fill) crumb, focus)

downC :: Crumb b -> ExprF a -> Maybe (Crumb a, a)
downC crumb expr
  = fmap (fillCrumb crumb)
  $ case (crumb, expr) of
        (AppFC Zero _, AppF x y)  -> Just (y, x)
        (AppFC One  _, AppF x y)  -> Just (x, y)
        (AbsFC n1,     AbsF n2 x) -> guard (n1 == n2) >> Just (x, x)
        _                         -> Nothing

upC :: Crumb Expr -> Expr -> Expr
upC (AppFC Zero e1) e0 = Fix $ AppF e0 e1
upC (AppFC One  e0) e1 = Fix $ AppF e0 e1
upC (AbsFC name)    e  = Fix $ AbsF name e

-- Expression Zipper
type ZipperG e = ([Crumb e], e)
type Zipper = ZipperG Expr

up :: Zipper -> Maybe Zipper
up ([],   _)    = Nothing
up (c:cs, expr) = Just (cs, upC c expr)

down :: Crumb b -> Zipper -> Maybe Zipper
down oldCrumb (trail, oldExpr) = do
    (crumb, expr) <- downC oldCrumb (project oldExpr)
    pure (crumb:trail, expr)

top :: Zipper -> Zipper
top z = case up z of
          Nothing -> z
          Just z' -> top z'

follow :: [Crumb b] -> Zipper -> Maybe Zipper
follow crumbs z = foldr (\crumb mz -> mz >>= down crumb) (pure z) (reverse crumbs)

toZipper :: Expr -> Zipper
toZipper = ([],)

-- Hatched Expressions
type HatchedF = Product ExprF Maybe
type Hatched = Fix HatchedF

pattern Hatch   expr hatch = Fix (Pair expr (Just hatch))
pattern NoHatch expr       = Fix (Pair expr Nothing)

type ZipperH = ZipperG Hatched

-- Examples:
s, k, i :: Expr
s = Abs "x" $ Abs "y" $ Abs "z" $ App (App (Var "x") (Var "z")) (App (Var "y") (Var "z"))
k = Abs "x" $ Abs "y" $ Var "x"
i = Abs "x" $ Var "x"
