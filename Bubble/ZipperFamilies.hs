-- Things that should be in Haskell 98 anyways:
{-# LANGUAGE TupleSections #-}
-- Advanced syntactical sugar:
{-# LANGUAGE PatternSynonyms #-}
-- GHC magic:
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Bubble.ZipperFamilies where

import Data.Void
import Data.Fix
import Data.Functor.Product
import Data.Functor.Const
import Data.Functor.Sum
import Data.Functor.Foldable
import Control.Monad

import Text.Show.Deriving (deriveShow1)

-- Expression base functor
type Expr = Fix ExprF

data ExprF a
    = AppF a a
    | AbsF String a
    | VarF String
    deriving (Show, Functor, Foldable, Traversable)

pattern App e0 e1  = Fix (AppF e0 e1)
pattern Abs name e = Fix (AbsF name e)
pattern Var name   = Fix (VarF name)

-- Crumbs for an Expression Zipper
data Two = Zero | One
    deriving (Show)
data ExprCrumb a
    = AppFC Two a
    | AbsFC String
    -- | VarFC Void
    deriving (Show, Functor)

-- Crumb class for fixpoints
class (Functor base, Functor crumb) => Crumb (base :: * -> *) (crumb :: * -> *) | base -> crumb where
    downC :: forall a b. crumb b -> base a -> Maybe (crumb a, a)
    upC :: forall b. crumb b -> b -> base b

fillCrumb :: Functor f => f a -> (b, b) -> (f b, b)
fillCrumb crumb (fill, focus) = (fmap (const fill) crumb, focus)

instance Crumb ExprF ExprCrumb where
    downC crumb expr
      = fmap (fillCrumb crumb)
      $ case (crumb, expr) of
            (AppFC Zero _, AppF x y)  -> Just (y, x)
            (AppFC One  _, AppF x y)  -> Just (x, y)
            (AbsFC n1,     AbsF n2 x) -> guard (n1 == n2) >> Just (x, x)
            _                         -> Nothing

    upC (AppFC Zero e1) e0 = AppF e0 e1
    upC (AppFC One  e0) e1 = AppF e0 e1
    upC (AbsFC name)    e  = AbsF name e

-- Expressions with Hatches
newtype ExprHF a = ExprHF (Product ExprF Maybe a)
    deriving Functor
type ExprH = Fix ExprHF

type ExprHCrumb = Product ExprCrumb Maybe

instance Crumb ExprHF ExprHCrumb where
    downC (Pair crumb _) (ExprHF (Pair expr hatch)) = do
        (newCrumb, newFocus) <- downC crumb expr
        pure (Pair newCrumb hatch, newFocus)
    upC (Pair crumb hatch) subexpr =
        let expr = upC crumb subexpr
         in ExprHF $ Pair expr hatch

--instance Crumb Maybe (Const ()) where
--    downC _ x    = fmap (Const (),) x
--    upC   _ expr = Fix $ Just expr
--
--instance (Crumb b1 c1, Crumb b2 c2) => Crumb (Product b1 b2) (Sum (Product b1 c2) (Product b2 c1)) where
--    downC (InL (Pair b1 c2)) = undefined
--    downC (InR (Pair b2 c1)) = undefined
--    upC   = undefined

    {-
-- Expression Zipper
type Zipper = ([Crumb Expr], Expr)

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

data CrumbZ a
    = L (Product Crumb Maybe a)
    | R (ExprF a)

-- Examples:
deriveShow1 ''ExprF

s, k, i :: Expr
s = Abs "x" $ Abs "y" $ Abs "z" $ App (App (Var "x") (Var "z")) (App (Var "y") (Var "z"))
k = Abs "x" $ Abs "y" $ Var "x"
i = Abs "x" $ Var "x"
    -}
