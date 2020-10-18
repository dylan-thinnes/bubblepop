{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
module Experiment.Simple where

import Text.Show.Deriving

import qualified Data.Map as M
import Data.Map (Map, (!?), insert, empty, fromList)
import Data.Fix (Fix(..))
import Data.Functor.Foldable

data ExprF b a
    = LitF Literal
    | AppF b a [a]
    | AbsF b [a] a
    | ConF b String
    | VarF b String
    | IfF  b a a a
    | LetF b String a a
    deriving (Show, Functor, Foldable, Traversable)

data Literal = Char Char | Int Int | String String | Bool Bool
    deriving (Show)

type Expr b = Fix (ExprF b)

data PrimOp = PrimOp String (forall a. [Expr a] -> Either String (Expr a))
instance Show PrimOp where
    show (PrimOp name _) = name

deriveShow1 ''ExprF

pattern Lit lit                  = Fix (LitF lit)
pattern If  ann cond true false  = Fix (IfF  ann cond true false)
pattern App ann function args    = Fix (AppF ann function args)
pattern Abs ann args body        = Fix (AbsF ann args body)
pattern Con ann name             = Fix (ConF ann name)
pattern Var ann name             = Fix (VarF ann name)
pattern Let ann formal real body = Fix (LetF ann formal real body)

newtype Env = Env { unenv :: Map String (Either (Expr Env) PrimOp) }
    deriving (Show)

-- Updating environments
get :: Env -> String -> Maybe (Either (Expr Env) PrimOp)
get (Env e) name = e !? name

set :: String -> Expr Env -> Env -> Env
set name expr (Env e) = Env $ insert name (Left expr) e

addPrimop :: PrimOp -> Env -> Env
addPrimop op@(PrimOp name _) (Env e) = Env $ insert name (Right op) e

-- Add environments to expressions
envs :: Expr () -> Env -> Expr Env
envs = cata f
    where
        f (LitF x) _ = Lit x
        f (IfF  () cond true false) env = If env (cond env) (true env) (false env)
        f (AppF () function args) env = App env (function env) (args <*> [env])
        f (AbsF () args body) env = Abs env (args <*> [env]) (body env)
        f (ConF () name) env = Con env name
        f (VarF () name) env = Var env name
        f (LetF () name sub body) env = let env' = set name (sub env) env in Let env' name (sub env) (body env)

baseEnv :: Env
baseEnv = foldr addPrimop (Env empty)
    [PrimOp "+" $ \case -- TODO: PARTIAL APPLICATION OF PRIMOPS
        [Lit (Int x), Lit (Int y)] -> Right $ Lit $ Int $ x + y
        [_, _]                     -> Left "Arguments of wrong type."
        _                          -> Left "Wrong number of arguments."
    ]

ex1 :: Expr ()
ex1 = App () (Var () "+") [Lit $ Int 1, Lit $ Int 2]

ex2 :: Expr ()
ex2 = If () (App () (Var () "f") [Var () "x", Var () "y"]) (Var () "x") (App () (Var () "+") [Var () "y", Lit $ Int 1])

    {-
apply :: Expr Env -> Either String (Expr Env)
apply = cata f
    where
        f :: ExprF Env (Either String (Expr Env)) -> Either String (Expr Env)
        f (LitF x) = Right $ Lit x
        f any = sequence any >>= g

        g :: ExprF Env (Expr Env) -> Either String (Expr Env)
        g (IfF _ cond true false) =
            case cond of
              (Lit (Bool b)) -> Right $ if b then true else false
              _              -> Left "Non-bool for if statement."
        g (AppF _ function arguments) =
            case function of
              _ -> undefined
        g (AbsF _ arguments body) = undefined
    -}
