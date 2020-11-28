{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Experiment.Fix2 where

import qualified Data.Map as M
import Data.Map (Map, (!?), insert, empty, fromList)
import Data.Bifunctor
import qualified Data.Bifunctor.Fix as Bi
import Data.Bifunctor.TH
import Data.Functor.Foldable hiding (Cons)
import Text.Show.Deriving
import Data.Fix (Fix(..))
import Data.Functor.Classes

data PrimOp = PrimOp String ([Expr] -> Either String Expr)
instance Show PrimOp where
    show (PrimOp name _) = name

-- ENVIRONMENTS
newtype Env = Env { unenv :: Map String (Either Expr PrimOp) }

get :: Env -> String -> Maybe (Either Expr PrimOp)
get (Env e) name = e !? name

set :: String -> Expr -> Env -> Env
set name expr (Env e) = Env $ insert name (Left expr) e

addPrimop :: PrimOp -> Env -> Env
addPrimop op@(PrimOp name _) (Env e) = Env $ insert name (Right op) e

-- EXPRESSIONS
data ExprF b a
    = LitF Literal
    | AppF (Maybe b) Env a [a]
    | AbsF (Maybe b) Env [a] a
    | VarF (Maybe b) Env String
    | IfF  (Maybe b) Env a a a
    | LetF (Maybe b) Env String a a
    deriving (Functor, Foldable, Traversable)

data Bifix f b = Bifix { biout :: f b (Bifix f b) }
instance Bifunctor f => Functor (Bifix f) where
    fmap f (Bifix x) = Bifix $ bimap f (fmap f) x

type Expr = Fix (Bifix ExprF)

data Literal = Char Char | Int Int | String String | Bool Bool
    deriving (Show)

deriveShow2 ''ExprF

instance Show2 p => Show1 (Bifix p) where
  liftShowsPrec sp1 sl1 p (Bifix x) = showParen (p > 10) $
      showString "In {out = "
    . liftShowsPrec2 sp1 sl1
                     (liftShowsPrec sp1 sl1) (liftShowList sp1 sl1)
                     0 x
    . showChar '}'

deriving instance (Show Env)
deriving instance (Show a, Show b) => Show (ExprF a b)

deriveBifunctor ''ExprF

type instance Base (Bifix f b) = f b
instance Functor (f b) => Recursive (Bifix f b) where
    project = biout
instance Functor (f b) => Corecursive (Bifix f b) where
    embed = Bifix

evalTree :: Bifix ExprF b -> Fix (Bifix ExprF)
evalTree = ana undefined
