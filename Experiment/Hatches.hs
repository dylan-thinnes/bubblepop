{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-unused-matches #-}

module Experiment.Hatches where

import qualified Data.Map as M
import Data.Map (Map, (!?), insert, fromList, delete)
import Data.Fix (Fix(..))
import Data.Functor.Foldable
import Text.Show.Deriving
import Data.Functor.Classes
import Data.Functor.Product
import Data.Functor.Compose
import Control.Monad (join, guard)
import Control.Monad.Free
import qualified Data.List.NonEmpty as N
import Data.List.NonEmpty (NonEmpty(..), (<|))
import Data.Functor ((<&>))

data PrimOp = PrimOp
    { primOpName :: String
    , primOpContract :: [LiteralType]
    , primOpFunc :: [Literal] -> Literal
    }
instance Show PrimOp where
    show (PrimOp name _ _) = name

-- EXPRESSIONS
type Expr = Fix ExprF

data ExprF a
    = LitF Literal
    | AppF a [a]
    | AbsF [String] a
    | VarF String
    | IfF  a a a
    | LetF String a a
    | PrimF PrimOp
    deriving (Functor, Foldable, Traversable)

-- Literals
data Literal = Char Char | Int Int | String String | Bool Bool
    deriving (Show)
data LiteralType = TChar | TInt | TString | TBool
    deriving (Show)

matchLit :: LiteralType -> Literal -> Bool
matchLit TChar   (Char _)   = True
matchLit TInt    (Int _)    = True
matchLit TString (String _) = True
matchLit TBool   (Bool _)   = True
matchLit _       _          = False

matchLits :: [LiteralType] -> [Literal] -> Bool
matchLits ts lits = length ts == length lits && and (zipWith matchLit ts lits)

toLit :: Expr -> Maybe Literal
toLit (Fix (LitF lit)) = Just lit
toLit _ = Nothing

-- Derive Show1 instance
deriveShow1 ''ExprF

-- Patterns
pattern Lit lit = Fix (LitF lit)
pattern App fun args = Fix (AppF fun args)
pattern Abs args body = Fix (AbsF args body)
pattern Var name = Fix (VarF name)
pattern If cond true false = Fix (IfF cond true false)
pattern Let name bound body = Fix (LetF name bound body)
pattern Prim prim = Fix (PrimF prim)

-- Environments
newtype Env = Env { unenv :: Map String Expr }
deriving instance Show Expr => Show Env

get :: Env -> String -> Maybe Expr
get (Env e) name = e !? name

set :: String -> Expr -> Env -> Env
set name expr (Env e) = Env $ insert name expr e

remove :: String -> Env -> Env
remove name (Env e) = Env $ delete name e

addPrimop :: PrimOp -> Env -> Env
addPrimop op@(PrimOp name _ _) = set name (Prim op)

empty :: Env
empty = Env (M.empty)

-- Crumbs and crumbtrails
data Crumb
    = AppFunc | AppArg Int
    | AbsBody
    | IfCond | IfTrue | IfFalse
    | LetBound | LetBody
    deriving (Show)

type Crumbtrail = [Crumb]

-- Simple name replace, can't handle name collisions...
replace :: (String, Expr) -> Expr -> Expr
replace (name, replacement) = cata f
    where
        f :: ExprF Expr -> Expr
        f v =
            case embed v of
              Var varName
                | varName == name -> replacement
                | otherwise       -> Var varName
              y -> y

crumbs :: Expr -> Env -> [Crumbtrail]
crumbs = cata f
    where
        f :: ExprF (Env -> [Crumbtrail]) -> Env -> [Crumbtrail]
        f = undefined

modify :: Expr -> Env -> Expr
modify = cata f
    where
    f :: ExprF (Env -> Expr) -> Env -> Expr
    f expr env = embed expr'
        where
            env' = modifyEnv expr' env
            expr' = fmap ($ env') expr

            modifyEnv :: ExprF Expr -> Env -> Env
            modifyEnv (LetF name expr _) = set name expr
            modifyEnv (AbsF names _)     = \env -> foldr remove env names
            modifyEnv _                  = id

-- Find "hatches" in the tree where we can replace a node
hatch :: Env -> ExprF Expr -> Maybe Expr
hatch _ (LitF _)    = Nothing -- Literals have no escape hatches
hatch _ (PrimF _) = Nothing -- PrimOps have no escape hatches
hatch e (VarF name) = get e name -- Variables have escape hatches when defined in the environment
hatch _ (IfF cond true false) =
    case cond of
      (Lit (Bool True))  -> Just true
      (Lit (Bool False)) -> Just false
      _                  -> Nothing
hatch _ (AppF func args) =
    case func of
      (Abs names body) ->
          -- Check args & names match, then place recursive `replace` into escape hatch
           if length args == length names
              then Just $ foldr replace body (zip names args)
              else Nothing -- signal error, rather than hide an escape hatch
      (Prim (PrimOp _ contract func)) -> do
          -- Check args are all literals & cardinality matches, then run
          lits <- traverse toLit args
          guard $ matchLits contract lits
          let result = func lits
          pure (Lit result)
      _ -> Nothing
hatch _ (AbsF args body) = -- Escape hatch if lambda has no remaining arguments, will become useful when AppF becomes curried/partial-aware
    if null args then Just body else Nothing
hatch _ (LetF name expr body) = -- Escape hatch at any point by substituting in the body - will need further logic when patterns are implemented
    Just body

-- Pretty print a tree
prettyStr :: Expr -> String
prettyStr = unlines . N.toList . cata f
    where
        line :: a -> NonEmpty a
        line = (:| [])

        nec :: [NonEmpty a] -> NonEmpty a
        nec = foldr1 (<>)

        indent :: NonEmpty String -> NonEmpty String
        indent = fmap ("  " ++)

        f :: ExprF (NonEmpty String) -> NonEmpty String
        f (LitF (Int i)) = line $ show i
        f (LitF (Char c)) = line $ show c
        f (LitF (String s)) = line $ show s
        f (LitF (Bool b)) = line $ show b
        f (AppF body args) = body <> indent (nec args)
        f (AbsF args body) = ("\\" ++ unwords args) <| indent body
        f (VarF name) = line name
        f (IfF cond true false) = line "if" <> indent cond <> line "then" <> indent true <> line "else" <> indent false
        f (PrimF op) = line $ show op
        f (LetF name bound body) = line ("let " ++ name ++ " =") <> indent bound <> line "in" <> indent body

-- Example
ex :: Expr
ex =
    If
        (App
            (Prim $ PrimOp "<" [TInt, TInt] (\[Int i, Int j] -> Bool $ i < j))
            [ (App
                (Prim $ PrimOp "*" [TInt, TInt] (\[Int i, Int j] -> Int $ i * j))
                [ Var "x"
                , Lit (Int 2)
                ])
            , Var "x"
            ])
        (Var "x")
        (Var "y")
