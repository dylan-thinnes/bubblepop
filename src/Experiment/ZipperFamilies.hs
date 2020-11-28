-- Things that should be in Haskell 98 anyways:
{-# LANGUAGE TupleSections #-}
-- Advanced syntactical sugar:
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
-- GHC magic:
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Experiment.ZipperFamilies where

import Prelude hiding (lookup)

import Data.Void
import Data.Functor.Product
import Data.Functor.Const
import Data.Functor.Sum
import Data.Functor.Foldable hiding (Cons)
import Control.Monad
import Data.Map (Map, lookup, insert, delete)
import Data.Fix (Fix(..))

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

pattern EHF expr hatch = ExprHF (Pair expr hatch)
pattern EH expr hatch = Fix (EHF expr hatch)

type ExprHCrumb = Product ExprCrumb Maybe

instance Crumb ExprHF ExprHCrumb where
    downC (Pair crumb _) (ExprHF (Pair expr hatch)) = do
        (newCrumb, newFocus) <- downC crumb expr
        pure (Pair newCrumb hatch, newFocus)
    upC (Pair crumb hatch) subexpr =
        let expr = upC crumb subexpr
         in ExprHF $ Pair expr hatch

-- Generic crumbs for functor products & maybe functor
-- Demonstrates product rule of derivative

--instance (Crumb b1 c1, Crumb b2 c2) => Crumb (Product b1 b2) (Sum (Product b1 c2) (Product b2 c1)) where
--    downC (InL (Pair b1 c2)) = undefined
--    downC (InR (Pair b2 c1)) = undefined
--    upC   = undefined

--instance Crumb Maybe (Const ()) where
--    downC _ x    = fmap (Const (),) x
--    upC   _ expr = Fix $ Just expr

-- Expression Zipper
type Zipper expr crumb = ([crumb (Fix expr)], Fix expr)

up :: Crumb expr crumb => Zipper expr crumb -> Maybe (Zipper expr crumb)
up ([],   _)    = Nothing
up (c:cs, expr) = Just (cs, Fix $ upC c expr)

down :: Crumb expr crumb => crumb any -> Zipper expr crumb -> Maybe (Zipper expr crumb)
down oldCrumb (trail, oldExpr) = do
    (crumb, expr) <- downC oldCrumb (project oldExpr)
    Just (crumb:trail, expr)

top :: Crumb expr crumb => Zipper expr crumb -> Zipper expr crumb
top z = case up z of
          Nothing -> z
          Just z' -> top z'

follow :: Crumb expr crumb => [crumb any] -> Zipper expr crumb -> Maybe (Zipper expr crumb)
follow crumbs z = foldr (\crumb mz -> mz >>= down crumb) (pure z) (reverse crumbs)

toZipper :: Fix expr -> Zipper expr crumb
toZipper = ([],)

-- Algebra transformations
liftCata :: (ExprF b -> a) -> (ExprHF b -> a)
liftCata alg (ExprHF (Pair expr _)) = alg expr

lowerAna :: (a -> ExprHF b) -> (a -> ExprF b)
lowerAna alg a = let (ExprHF (Pair expr _)) = alg a in expr

type Env = Map String ExprH

--refine :: ExprF (Env -> ExprH) -> (Env -> ExprH)
--refine expr env = Fix $ memo env $ modifyEnv expr env
--    where
--    memo :: Env -> ExprF ExprH -> ExprHF ExprH
--    memo env x = ExprHF $ Pair x (envHatch env x)
--
--    modifyEnv :: ExprF (Env -> ExprH) -> Env -> ExprF ExprH
--    modifyEnv (CaseF scrutee branches) env = CaseF (scrutee env) (map handleBranch branches)
--        where
--            handleBranch (pat, branch) = (pat, branch $ foldr remove env (patternNames pat))
--    modifyEnv f                        env = ($ env) <$> f

envHatch :: Env -> ExprF ExprH -> Maybe ExprH
envHatch env (VarF e) = lookup e env
envHatch _   expr     = rehatch expr

rehatch :: ExprF ExprH -> Maybe ExprH
rehatch (VarF _) = Nothing
rehatch (AbsF _ _) = Nothing
rehatch (AppF fun arg) =
    case fun of
      EH (AbsF name body) _ -> Just $ replace body (name, arg)
      _                     -> Nothing

replaceF :: ExprHF (ExprH, (String, ExprH) -> ExprH) -> (String, ExprH) -> ExprH
replaceF (EHF expr paraHatch) replacement@(name, value) =
    let hatch = fmap fst paraHatch
    in
    case expr of
      VarF n                    -> if name == n
                                      then value
                                      else EH (VarF n) hatch
      AbsF n (oldBody, newBody) -> if name == n
                                      then EH (AbsF n oldBody) hatch
                                      else EH (AbsF n (newBody replacement)) hatch
      AppF (_, fun) (_, arg)   -> EH (AppF (fun replacement) (arg replacement)) hatch
replaceF _ _ = undefined -- Not sure why GHC is giving me an inexhaustive match here...

replace = para replaceF

-- Examples:
deriveShow1 ''ExprF

s, k, i :: Expr
s = Abs "x" $ Abs "y" $ Abs "z" $ App (App (Var "x") (Var "z")) (App (Var "y") (Var "z"))
k = Abs "x" $ Abs "y" $ Var "x"
i = Abs "x" $ Var "x"
