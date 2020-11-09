{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-unused-matches #-}

module Bubble.Expr where

import qualified Data.Map as M
import Data.Map (Map, (!?), insert, fromList, delete)
import Data.Functor.Foldable hiding (Cons)
import Text.Show.Deriving (deriveShow1)
import Data.Functor.Product (Product(..))
import Data.Functor.Const (Const(..))
import Control.Monad (join, guard)
import Data.Functor ((<&>))
import GHC.Exts (IsString(..))
import qualified Data.Foldable
import Control.Applicative
import Data.Char (isUpper)
import Data.Functor.Compose

{------------------------------------------------------------------------------
                                RAW EXPRESSIONS
                         expressions without behaviour
------------------------------------------------------------------------------}

type RawExpr = Fix RawExprF

data RawExprF a
    = LitF Literal
    | AppF Fixity a [a]
    | AbsF [Name] a
    | VarF Name
    | IfF  a a a
    | EConsF (Cons a)
    | CaseF a [(Pattern Name, a)]
    | LetF Name a a
    | PrimOpF PrimOp -- Primops
    | AnnF String a -- Annotations
    deriving (Functor, Foldable, Traversable)

-- Pattern synonyms for fixpoint RawExpr
pattern LitR lit = Fix (LitF lit)
pattern AppR fixity fun args = Fix (AppF fixity fun args)
pattern AbsR args body = Fix (AbsF args body)
pattern VarR name = Fix (VarF name)
pattern IfR cond true false = Fix (IfF cond true false)
pattern LetR name bound body = Fix (LetF name bound body)
pattern EConsR name args = Fix (EConsF (Cons name args))
pattern CaseR scrut branches = Fix (CaseF scrut branches)
pattern PrimOpR prim = Fix (PrimOpF prim)
pattern AnnR name cont = Fix (AnnF name cont)

-- Names
data Name = Name
    { string :: String
    , fixity :: Fixity
    , variety :: Variety
    }
    deriving (Show, Eq)
data Fixity = Infix | Prefix
    deriving (Show, Eq)
data Variety = Con | Var
    deriving (Show, Eq)

prettyName Name {..} targetFixity
  = case (targetFixity, fixity) of
      (Prefix, Infix) -> "(" ++ string ++ ")"
      (Infix, Prefix) -> "`" ++ string ++ "`"
      _               -> string

instance IsString Name where
    fromString name = Name name fixity variety
        where
        special x = elem x ("!#$%&*+./<=>?@\\^|-~:" :: String)
        fixity = if special (head name) then Infix else Prefix
        variety = case fixity of
                    Infix -> if elem ':' name then Con else Var
                    Prefix -> if isUpper (head name) then Con else Var

-- Primitive operations
data PrimOp = PrimOp
    { primOpName :: Name
    , primOpContract :: [LiteralType]
    , primOpFunc :: [Literal] -> Literal
    }
instance Show PrimOp where
    show (PrimOp name _ _) = string name

-- Constructors
data Cons a = Cons Name [a]
    deriving (Show, Functor, Foldable, Traversable)

-- Patterns to match with
data Pattern a
    = PCons (Cons (Pattern a))
    | PWildcard
    | PLiteral Literal
    | PEscape a
    deriving (Show, Functor, Foldable, Traversable)

prettyPat :: Pattern Name -> String
prettyPat (PCons (Cons name args)) =
    let prettyArgs = prettyPat <$> args
    in
    if fixity name == Infix
       then unwords $ case prettyArgs of
                        (a1:aRest) -> a1 : string name : aRest
                        []         -> [string name]
       else unwords (string name : prettyArgs)
prettyPat PWildcard = "_"
prettyPat (PLiteral lit) = prettyLit lit
prettyPat (PEscape a) = string a

patternNames :: Pattern Name -> [String]
patternNames pat = string <$> Data.Foldable.toList pat

instance IsString (Pattern String) where
    fromString = PEscape

-- Literals
data Literal = Char Char | Int Int | String String | Bool Bool
    deriving (Eq, Show)
data LiteralType = TChar | TInt | TString | TBool
    deriving (Eq, Show)

prettyLit :: Literal -> String
prettyLit (Int i) = show i
prettyLit (Char c) = show c
prettyLit (String s) = show s
prettyLit (Bool b) = show b

matchLit :: LiteralType -> Literal -> Bool
matchLit TChar   (Char _)   = True
matchLit TInt    (Int _)    = True
matchLit TString (String _) = True
matchLit TBool   (Bool _)   = True
matchLit _       _          = False
matchLits :: [LiteralType] -> [Literal] -> Bool
matchLits ts lits = length ts == length lits && and (zipWith matchLit ts lits)

{------------------------------------------------------------------------------
                              REFINED EXPRESSIONS
               with "hatches", provided by an environment closure
------------------------------------------------------------------------------}

type Expr f = Fix (ExprF f)
type ExprF f = Product RawExprF f

newtype Redex a = R { unR :: Maybe a }
    deriving (Functor, Foldable, Traversable)

pattern Redex a = R (Just a)
pattern NoRedex = R Nothing

maybeToRedex :: Maybe a -> Redex a
maybeToRedex = R

-- Pattern synonyms for refined expressions
pattern LitG hatch lit             = Fix (Pair (LitF lit)             hatch)
pattern AppG hatch fixity fun args = Fix (Pair (AppF fixity fun args) hatch)
pattern AbsG hatch args body       = Fix (Pair (AbsF args body)       hatch)
pattern VarG hatch name            = Fix (Pair (VarF name)            hatch)
pattern IfG hatch cond true false  = Fix (Pair (IfF cond true false)  hatch)
pattern LetG hatch name bound body = Fix (Pair (LetF name bound body) hatch)
pattern EConsG hatch cons          = Fix (Pair (EConsF cons)          hatch)
pattern CaseG hatch scrut branches = Fix (Pair (CaseF scrut branches) hatch)
pattern PrimOpG hatch prim         = Fix (Pair (PrimOpF prim)         hatch)
pattern AnnG hatch text cont       = Fix (Pair (AnnF text cont)       hatch)

-- Possibly extract the literal in a refined expression
toLit :: Expr f -> Maybe Literal
toLit (Fix (Pair (LitF lit) _)) = Just lit
toLit _ = Nothing

-- Match a refined expression against a pattern
matchPat :: Pattern Name -> Expr f -> Maybe [(String, Expr f)]
matchPat (PCons (Cons consFormal formals)) (EConsG _ (Cons consReal reals))
    = do
        guard $ string consFormal == string consReal
        guard $ length formals == length reals
        matchings <- sequence $ zipWith matchPat formals reals
        pure $ concat matchings
matchPat PWildcard expr = Just []
matchPat (PLiteral formal) (LitG _ real) = guard (formal == real) >> pure []
matchPat (PEscape formal) real = pure $ [(string formal, real)]
matchPat _ _ = Nothing

{------------------------------------------------------------------------------
                                  ENVIRONMENTS
------------------------------------------------------------------------------}

newtype Env = Env { unenv :: Map String (Expr Redex) }

get :: Env -> String -> Redex (Expr Redex)
get (Env e) name = maybeToRedex $ e !? name

set :: String -> (Expr Redex) -> Env -> Env
set name expr (Env e) = Env $ insert name expr e

remove :: String -> Env -> Env
remove name (Env e) = Env $ delete name e

addPrimop :: PrimOp -> Env -> Env
addPrimop op@(PrimOp name _ _) = set (string name) (Fix $ Pair (PrimOpF op) NoRedex)

empty :: Env
empty = Env (M.empty)

-- Simple replace, can't handle name collisions...
replace :: (String, Expr Redex) -> Expr Redex -> Expr Redex
replace (name, replacement) = para f
    where
        f :: ExprF Redex (Expr Redex, Expr Redex) -> Expr Redex
        f v =
            let unchanged = embed $ fst <$> v
                changed   = embed $ snd <$> v
            in
            case v of
              Pair (VarF varName) NoRedex
                | name == string varName -> replacement
                | otherwise              -> unchanged
              Pair (LetF letName _ _) _
                | name == string letName -> unchanged
                | otherwise              -> changed
              Pair (AbsF names _) _
                | name `elem` map string names -> unchanged
                | otherwise                    -> changed
              Pair (CaseF scrutee branches) hatch
                -> CaseG (snd <$> hatch) (snd scrutee) 
                    $ branches <&> \(pat, body)
                                    -> ( pat
                                       , if name `elem` patternNames pat
                                           then fst body
                                           else snd body
                                       )
              _ -> changed

{------------------------------------------------------------------------------
                             REFINEMENT & RUINATION
                      where RawExprs & Exprs trade places
------------------------------------------------------------------------------}

-- Refine a RawExpr into a refined Expr, by binding environments and attaching escape hatches
refine :: RawExpr -> (Env -> Expr Redex)
refine = cata f
    where
        f :: RawExprF (Env -> Expr Redex) -> (Env -> Expr Redex)
        f expr env = Fix $ memo env $ modifyEnv expr env

        memo :: Env -> RawExprF (Expr Redex) -> ExprF Redex (Expr Redex)
        memo env x = Pair x (envHatch env x)

        modifyEnv :: RawExprF (Env -> Expr Redex) -> Env -> RawExprF (Expr Redex)
        --modifyEnv (LetF name expr body)    env = LetF name expr' (body $ remove (string name) env')
        modifyEnv (LetF name expr body)    env = LetF name expr' (body env')
            where
                env' = set (string name) expr' env
                expr' = expr env'
        modifyEnv (AbsF names body)        env = AbsF names $ body $ foldr remove env $ map string names
        modifyEnv (CaseF scrutee branches) env = CaseF (scrutee env) (map handleBranch branches)
            where
                handleBranch (pat, branch) = (pat, branch $ foldr remove env (patternNames pat))
        modifyEnv f                        env = ($ env) <$> f

        envHatch :: Env -> RawExprF (Expr Redex) -> Redex (Expr Redex)
        envHatch env expr@(VarF name) = rehatch (get env (string name)) expr -- Supply env-defined variable as a prehatch
        envHatch _ expr = rehatch NoRedex expr

rerefine :: Expr Redex -> Expr Redex
rerefine = cata (\(Pair expr prehatch) -> Fix $ Pair expr (rehatch prehatch expr))

-- "Algebra" that determines any new escape hatches, using the "previous"
-- escape hatch & the current expression
rehatch :: Redex (Expr Redex) -> RawExprF (Expr Redex) -> Redex (Expr Redex)
rehatch prehatch (VarF name) = prehatch -- Variables have escape hatches when predefined in the environment
rehatch _ (LitF _)    = NoRedex -- Literals have no escape hatches
rehatch _ (PrimOpF _) = NoRedex -- PrimOps have no escape hatches
rehatch _ (EConsF _)  = NoRedex -- Constructors have no escape hatches
rehatch _ (AnnF "autorun" (Fix (Pair _ hatch))) = hatch -- Other annotations have no escape hatches
rehatch _ (AnnF _ _) = NoRedex -- Other annotations have no escape hatches
rehatch _ (IfF cond true false) =
    case cond of
      (Fix (Pair (LitF (Bool True)) _))  -> Redex true
      (Fix (Pair (LitF (Bool False)) _)) -> Redex false
      _                                  -> NoRedex
rehatch prehatch (AppF fixity func args) =
    case func of
      (AbsG _ names body) ->
          -- Check args & names match, then place recursive `replace` into escape hatch
           if length args == length names
              then Redex $ foldr replace body (zip (map string names) args)
              else NoRedex -- TODO: signal error, rather than hide an escape hatch
      (PrimOpG _ (PrimOp _ contract func)) -> maybeToRedex $ do
          -- Check args are all literals & cardinality matches, then run
          lits <- traverse toLit args
          guard $ matchLits contract lits
          let result = func lits
          pure $ LitG NoRedex result
      (VarG (Redex (AnnG _ "autoapply" e)) _) ->
          rehatch prehatch (AppF fixity e args)
      (AnnG _ "autoapply" e) ->
          rehatch prehatch (AppF fixity e args)
      _ -> NoRedex
rehatch _ (AbsF args body) = -- Escape hatch if lambda has no remaining arguments, will become useful when AppF becomes curried/partial-aware
    if null args then Redex body else NoRedex
rehatch _ (LetF name expr body) = -- Escape hatch at any point by substituting in the body - will need further logic when patterns are implemented
    --Redex $ replace (string name, expr) body
    Redex body
rehatch _ (CaseF scrutee branches) = -- Escape hatch when a pattern matches the scrutee
    let f [] = NoRedex
        f ((pat, body):rest) =
            case matchPat pat scrutee of
              Nothing -> f rest
              Just replacements -> Redex $ foldr replace body replacements
     in f branches

-- Remove all autorun nodes that can be
autorun :: Expr Redex -> Expr Redex
autorun = cata f
    where
        f (Pair (AnnF "autorun" (Fix (Pair _ (Redex hatch)))) _) = hatch
        f e = embed e

-- Ruin a refined Expr, casting it back into a RawExpr
ruin :: Expr Redex -> RawExpr
ruin = cata (\(Pair raw hatch) -> embed raw)

-- Derive show instances, needed for environments
deriveShow1 ''Cons
deriveShow1 ''RawExprF
deriveShow1 ''Redex
deriving instance Show (Expr Redex) => Show Env
