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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-unused-matches #-}

module Experiment.Patterns where

import qualified Data.Map as M
import Data.Map (Map, (!?), insert, fromList, delete)
import Data.Functor.Foldable hiding (Cons)
import Text.Show.Deriving (deriveShow1)
import Data.Functor.Product (Product(..))
import Control.Monad (join, guard)
import qualified Data.List.NonEmpty as N
import Data.List.NonEmpty (NonEmpty(..), (<|))
import Data.Functor ((<&>))
import GHC.Exts (IsString(..))
import qualified Data.Foldable
import Data.Char (isUpper)

{------------------------------------------------------------------------------
                                RAW EXPRESSIONS
                         expressions without behaviour
------------------------------------------------------------------------------}

type RawExpr = Fix RawExprF

data RawExprF a
    = LitF Literal
    | AppF a [a]
    | AbsF [String] a
    | VarF String
    | IfF  a a a
    | EConsF (Cons a)
    | CaseF a [(Pattern Name, a)]
    | LetF Name a a
    | PrimOpF PrimOp
    deriving (Functor, Foldable, Traversable)

-- Pattern synonyms for fixpoint RawExpr
pattern LitR lit = Fix (LitF lit)
pattern AppR fun args = Fix (AppF fun args)
pattern AbsR args body = Fix (AbsF args body)
pattern VarR name = Fix (VarF name)
pattern IfR cond true false = Fix (IfF cond true false)
pattern LetR name bound body = Fix (LetF name bound body)
pattern EConsR name args = Fix (EConsF (Cons name args))
pattern CaseR scrut branches = Fix (CaseF scrut branches)
pattern PrimOpR prim = Fix (PrimOpF prim)

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
  = if targetFixity == Prefix && fixity == Infix then "(" ++ string ++ ")" else string

instance IsString Name where
    fromString name = Name name fixity variety
        where
        special x = elem x ("!#$%&⋆+./<=>?@\\^|-~:" :: String)
        fixity = if special (head name) then Infix else Prefix
        variety = case fixity of
                    Infix -> if elem ':' name then Con else Var
                    Prefix -> if isUpper (head name) then Con else Var

-- Primitive operations
data PrimOp = PrimOp
    { primOpName :: String
    , primOpContract :: [LiteralType]
    , primOpFunc :: [Literal] -> Literal
    }
instance Show PrimOp where
    show (PrimOp name _ _) = name

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
             with "hatches", provided by an environment closure at
------------------------------------------------------------------------------}

type Expr = Fix ExprF
type ExprF = Product RawExprF Maybe

-- Pattern synonyms for refined expressions
pattern LitG hatch lit             = Fix (Pair (LitF lit)             hatch)
pattern AppG hatch fun args        = Fix (Pair (AppF fun args)        hatch)
pattern AbsG hatch args body       = Fix (Pair (AbsF args body)       hatch)
pattern VarG hatch name            = Fix (Pair (VarF name)            hatch)
pattern IfG hatch cond true false  = Fix (Pair (IfF cond true false)  hatch)
pattern LetG hatch name bound body = Fix (Pair (LetF name bound body) hatch)
pattern EConsG hatch cons          = Fix (Pair (EConsF cons)          hatch)
pattern CaseG hatch scrut branches = Fix (Pair (CaseF scrut branches) hatch)
pattern PrimOpG hatch prim         = Fix (Pair (PrimOpF prim)         hatch)

-- Possibly extract the literal in a refined expression
toLit :: Expr -> Maybe Literal
toLit (Fix (Pair (LitF lit) _)) = Just lit
toLit _ = Nothing

-- Match a refined expression against a pattern
matchPat :: Pattern Name -> Expr -> Maybe [(String, Expr)]
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

newtype Env = Env { unenv :: Map String Expr }

get :: Env -> String -> Maybe Expr
get (Env e) name = e !? name

set :: String -> Expr -> Env -> Env
set name expr (Env e) = Env $ insert name expr e

remove :: String -> Env -> Env
remove name (Env e) = Env $ delete name e

addPrimop :: PrimOp -> Env -> Env
addPrimop op@(PrimOp name _ _) = set name (Fix $ Pair (PrimOpF op) Nothing)

empty :: Env
empty = Env (M.empty)

-- Simple replace, can't handle name collisions...
replace :: (String, Expr) -> Expr -> Expr
replace (name, replacement) = para f
    where
        f :: ExprF (Expr, Expr) -> Expr
        f v =
            let unchanged = embed $ fst <$> v
                changed   = embed $ snd <$> v
            in
            case v of
              Pair (VarF varName) Nothing
                | name == varName -> replacement
                | otherwise       -> Fix $ Pair (VarF varName) Nothing
              Pair (LetF letName _ _) _
                | name == string letName -> unchanged
                | otherwise              -> changed
              Pair (AbsF names _) _
                | name `elem` names -> unchanged
                | otherwise         -> changed
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
                                  BREADCRUMBS
                         for indexing into expressions
------------------------------------------------------------------------------}

data Crumb
    = AppFunc | AppArg Int
    | AbsBody
    | IfCond | IfTrue | IfFalse
    | LetBound -- | LetBody
    | EConsArg Int
    | CaseBody | CaseBranch Int
    deriving (Show)

type Crumbtrail = [Crumb]

-- Find all crumbtrails in an expression tree
crumbtrails :: Expr -> [Crumbtrail]
crumbtrails = cata f
    where
        f :: ExprF [Crumbtrail] -> [Crumbtrail]
        f (Pair expr hatch) = children expr <> hasHatch hatch

        children :: RawExprF [Crumbtrail] -> [Crumbtrail]
        children (LitF lit) = []
        children (PrimOpF op) = []
        children (VarF name) = []
        children (AppF fun args) = ((AppFunc :) <$> fun) <> join (zipWith (fmap . (:)) (map AppArg [0..]) args)
        children (AbsF names body) = (AbsBody :) <$> body
        children (IfF cond true false) = join $ zipWith (fmap . (:)) [IfCond, IfTrue, IfFalse] [cond, true, false]
        children (LetF name bound body) = ((LetBound :) <$> bound) -- <> ((LetBody :) <$> body)
        children (EConsF (Cons _ args)) = join (zipWith (fmap . (:)) (map EConsArg [0..]) args)
        children (CaseF body branches) = ((CaseBody :) <$> body) <> join (zipWith (fmap . (:)) (map CaseBranch [0..]) (fmap snd branches))

        hasHatch :: Maybe a -> [Crumbtrail]
        hasHatch Nothing = []
        hasHatch (Just _) = [[]]

-- Follows a breadcrumb to its end-node, then replaces that node with its
-- escape hatch
hansel :: Expr -> (Crumbtrail -> Either String Expr)
hansel = para f
    where
        update :: [a] -> Int -> a -> [a]
        update xs i a = zipWith (\j x -> if i == j then a else x) [0..] xs

        f :: ExprF (Expr, Crumbtrail -> Either String Expr) -> Crumbtrail -> Either String Expr
        f (Pair expr hatch) trail =
            case trail of
              [] -> case hatch of
                      Just replacement -> Right $ fst replacement
                      Nothing -> Left "Tried to take a nonexistent escape hatch!"
              (crumb:rest)
                 -> fmap (Fix . (`Pair` (fst <$> hatch))) $
                     case (expr, crumb) of
                      (AppF func as,   AppFunc)  -> sequence $ AppF (snd func rest) (pure . fst <$> as) -- A lens, a lens! My kingdom for a lens!
                      (AppF f args,    AppArg i) ->
                          if i < length args
                             then sequence $ AppF (pure $ fst f) (update (pure . fst <$> args) i (snd (args !! i) rest)) -- Updates, updates, everywhere, but not a lens to see
                             else Left $ "Tried to follow a crumb to a nonexistent function argument, " ++ show (length args) ++ " " ++ show i
                      (AbsF x body,    AbsBody)  -> sequence $ AbsF x (snd body rest)
                      (IfF cond t f,   IfCond)   -> sequence $ IfF (snd cond rest) (pure $ fst t) (pure $ fst f)
                      (IfF c true f,   IfTrue)   -> sequence $ IfF (pure $ fst c) (snd true rest) (pure $ fst f)
                      (IfF c t false,  IfFalse)  -> sequence $ IfF (pure $ fst c) (pure $ fst t) (snd false rest)
                      (LetF n bound b, LetBound) -> sequence $ LetF n (snd bound rest) (pure $ fst b)
                      --(LetF n b body,  LetBody)  -> sequence $ LetF n (pure $ fst b) (snd body rest)
                      (EConsF (Cons name args), EConsArg i) ->
                          if i < length args
                             then sequence $ EConsF $ Cons name (update (pure . fst <$> args) i (snd (args !! i) rest))
                             else Left $ "Tried to follow a crumb to a nonexistent constructor argument, " ++ show (length args) ++ " " ++ show i
                      (CaseF body as,  CaseBody) -> sequence $ CaseF (snd body rest) (fmap (pure . fst) <$> as)
                      (CaseF b args, CaseBranch i) ->
                          if i < length args
                             then sequence $ CaseF (pure $ fst b) (update (fmap (pure . fst) <$> args) i (fmap (($ rest) . snd) (args !! i)))
                             else Left $ "Tried to follow a crumb to a nonexistent constructor argument, " ++ show (length args) ++ " " ++ show i
                      _                          -> Left "Incompatible crumb and constructor."

{------------------------------------------------------------------------------
                             REFINEMENT & RUINATION
                      where RawExprs & Exprs trade places
------------------------------------------------------------------------------}

-- Refine a RawExpr into a refined Expr, by binding environments and attaching escape hatches
refine :: RawExpr -> (Env -> Expr)
refine = cata f
    where
        f :: RawExprF (Env -> Expr) -> (Env -> Expr)
        f expr env = Fix $ memo env $ modifyEnv expr env

        memo :: Env -> RawExprF Expr -> ExprF Expr
        memo env x = Pair x (envHatch env x)

        modifyEnv :: RawExprF (Env -> Expr) -> Env -> RawExprF Expr
        modifyEnv (LetF name expr body)    env = LetF name expr' (body $ remove (string name) env')
            where
                env' = set (string name) expr' env
                expr' = expr env'
        modifyEnv (AbsF names body)        env = AbsF names $ body $ foldr remove env names
        modifyEnv (CaseF scrutee branches) env = CaseF (scrutee env) (map handleBranch branches)
            where
                handleBranch (pat, branch) = (pat, branch $ foldr remove env (patternNames pat))
        modifyEnv f                        env = ($ env) <$> f

        envHatch :: Env -> RawExprF Expr -> Maybe Expr
        envHatch env expr@(VarF name) = rehatch (get env name) expr -- Supply env-defined variable as a prehatch
        envHatch _ expr = rehatch Nothing expr

rerefine :: Expr -> Expr
rerefine = cata (\(Pair expr prehatch) -> Fix $ Pair expr (rehatch prehatch expr))

-- "Algebra" that determines any new escape hatches, using the "previous"
-- escape hatch & the current expression
rehatch :: Maybe Expr -> RawExprF Expr -> Maybe Expr
rehatch prehatch (VarF name) = prehatch -- Variables have escape hatches when predefined in the environment
rehatch _ (LitF _)    = Nothing -- Literals have no escape hatches
rehatch _ (PrimOpF _) = Nothing -- PrimOps have no escape hatches
rehatch _ (EConsF _)  = Nothing -- Constructors have no escape hatches
rehatch _ (IfF cond true false) =
    case cond of
      (Fix (Pair (LitF (Bool True)) _))  -> Just true
      (Fix (Pair (LitF (Bool False)) _)) -> Just false
      _                                  -> Nothing
rehatch _ (AppF func args) =
    case func of
      (Fix (Pair (AbsF names body) _)) ->
          -- Check args & names match, then place recursive `replace` into escape hatch
           if length args == length names
              then Just $ foldr replace body (zip names args)
              else Nothing -- signal error, rather than hide an escape hatch
      (Fix (Pair (PrimOpF (PrimOp _ contract func)) _)) -> do
          -- Check args are all literals & cardinality matches, then run
          lits <- traverse toLit args
          guard $ matchLits contract lits
          let result = func lits
          pure (Fix (Pair (LitF result) Nothing))
      _ -> Nothing
rehatch _ (AbsF args body) = -- Escape hatch if lambda has no remaining arguments, will become useful when AppF becomes curried/partial-aware
    if null args then Just body else Nothing
rehatch _ (LetF name expr body) = -- Escape hatch at any point by substituting in the body - will need further logic when patterns are implemented
    Just $ replace (string name, expr) body
rehatch _ (CaseF scrutee branches) = -- Escape hatch when a pattern matches the scrutee
    let f [] = Nothing
        f ((pat, body):rest) =
            case matchPat pat scrutee of
              Nothing -> f rest
              Just replacements -> Just $ foldr replace body replacements
     in f branches

-- Ruin a refined Expr, casting it back into a RawExpr
ruin :: Expr -> RawExpr
ruin = cata (\(Pair raw hatch) -> embed raw)

{------------------------------------------------------------------------------
                             IO & USER INTERACTION
------------------------------------------------------------------------------}

prettyRaw :: RawExpr -> String
prettyRaw = unlines . N.toList . cata toLines
    where
        line :: a -> NonEmpty a
        line = (:| [])

        nec :: [NonEmpty a] -> NonEmpty a
        nec = foldr1 (<>)

        nec' :: a -> [NonEmpty a] -> NonEmpty a
        nec' x xs = x :| concat (N.toList <$> xs)

        indent :: Functor f => f String -> f String
        indent = fmap ("  " ++)

        parenthesize :: NonEmpty String -> NonEmpty String
        parenthesize x = ("(" :| []) `fuse` x `fuse` (")" :| [])

        fuse :: NonEmpty String -> NonEmpty String -> NonEmpty String
        fuse (a :| []) (b :| bs) = (a ++ b) :| bs
        fuse (a :| as) (b :| bs) = a :| (init as ++ [last as ++ b] ++ bs)

        toLines :: RawExprF (NonEmpty String) -> NonEmpty String
        toLines (LitF lit) = line $ prettyLit lit
        toLines (AppF body args) = body <> indent (nec args)
        toLines (AbsF args body) = parenthesize $ ("\\" ++ unwords args ++ " ->") <| indent body
        toLines (VarF name) = line name
        toLines (IfF cond true false) = line "if" <> indent cond <> line "then" <> indent true <> line "else" <> indent false
        toLines (PrimOpF op) = line $ show op
        toLines (LetF name bound body) = line ("let " ++ prettyName name Prefix ++ " =") <> indent bound <> line "in" <> indent body
        toLines (EConsF (Cons name args)) =
            case fixity name of -- Very messy...
              Prefix -> nec' (prettyName name Prefix) (indent <$> args)
              Infix  -> case args of
                          (x:y:xs) ->
                              if length x <= 1
                                  then x `fuse` line (prettyName name Infix) `fuse` nec (y:xs)
                                  else x <> indent (nec' (prettyName name Infix) xs)
                          (x:[]) ->
                              if length x <= 1
                                  then parenthesize $ x `fuse` line (prettyName name Infix)
                                  else x <> indent (line (prettyName name Infix))
                          ([]) -> line (prettyName name Prefix)
        toLines (CaseF scrutee branches) = parenthesize $ line "case" <> indent scrutee <> nec' "of" (indent . handleBranch <$> branches)
            where
                handleBranch (pat, body) = line (prettyPat pat ++ " ->") <> indent body

pretty :: Either String Expr -> IO ()
pretty = \case
    Left e -> putStrLn $ "Error: " ++ e
    Right e -> putStrLn $ prettyRaw $ ruin e

repl :: String -> Expr -> IO Expr
repl str expr = do
    putStr "\ESC[2J\ESC[H"
    putStrLn "============================================"
    putStrLn str
    putStrLn $ prettyRaw $ ruin expr
    let options = crumbtrails expr
    if null options then pure expr
        else do
            mapM_ (uncurry showOption) (zip [0..] options)
            i <- readLn
            if | i < 0 -> pure expr
               | i >= length options -> repl "Error: Option index out of bounds." expr
               | otherwise -> do
                    let crumb = options !! i
                    case hansel expr crumb of
                      Left err -> repl ("Error: " ++ err) expr
                      Right newExpr -> repl "Success." $ rerefine newExpr
    where
        showOption i option = putStr (show i ++ ": ") >> print option

-- Derive show instances, needed for environments
deriveShow1 ''Cons
deriveShow1 ''RawExprF
deriving instance Show Expr => Show Env

-- Example
env :: Env
env = set "x" (Fix (Pair (LitF (Int 3)) Nothing)) empty

primEQ    = PrimOpR $ PrimOp "=" [TInt, TInt] (\[Int i, Int j] -> Bool $ i == j)
primLT    = PrimOpR $ PrimOp "<" [TInt, TInt] (\[Int i, Int j] -> Bool $ i < j)
primTimes = PrimOpR $ PrimOp "*" [TInt, TInt] (\[Int i, Int j] -> Int $ i * j)
primPlus  = PrimOpR $ PrimOp "+" [TInt, TInt] (\[Int i, Int j] -> Int $ i + j)
primMinus = PrimOpR $ PrimOp "-" [TInt, TInt] (\[Int i, Int j] -> Int $ i - j)

ex_simple :: RawExpr
ex_simple =
    IfR
        (AppR
            primLT
            [ (AppR
                primTimes
                [ VarR "x"
                , LitR (Int 2)
                ])
            , (AppR
                primTimes
                [ LitR (Int 5)
                , LitR (Int 7)
                ])
            ])
        (VarR "x")
        (VarR "y")

ex_simple' = refine ex_simple env

ex_fix :: RawExpr
ex_fix =
    LetR "x" (AppR (VarR "f") [VarR "x"]) (VarR "x")

ex_fix' = refine ex_fix env

ex_lambda :: RawExpr
ex_lambda =
    LetR "plusTwo"
        (AbsR ["y"] (AppR primPlus [LitR (Int 2), (VarR "y")]))
        (AppR primTimes [AppR (VarR "plusTwo") [VarR "x"], LitR (Int 3)])

ex_lambda' = refine ex_lambda env

ex_fac :: RawExpr
ex_fac =
    LetR "fac"
        (AbsR ["i"]
            (IfR
                (AppR primLT
                    [VarR "i"
                    ,LitR (Int 1)
                    ])
                (LitR (Int 1))
                (AppR primTimes
                    [VarR "i"
                    ,AppR (VarR "fac")
                        [AppR primMinus
                            [VarR "i"
                            ,LitR (Int 1)
                            ]]])))
        (AppR (VarR "fac") [LitR (Int 3)])

ex_fac' = refine ex_fac empty

ex_foldr :: RawExpr
ex_foldr =
    LetR "foldr"
        (AbsR ["f", "base", "list"]
            (CaseR (VarR "list")
                [(PCons (Cons ":" [PEscape "head", PEscape "rest"]),
                    AppR (VarR "f") [VarR "head", (AppR (VarR "foldr") [VarR "f", VarR "base", VarR "rest"])])
                ,(PCons (Cons "[]" []),
                    VarR "base")
                ]))
        (AppR (VarR "foldr") [primPlus, LitR (Int 7), EConsR ":" [LitR (Int 2), EConsR ":" [LitR (Int 3), EConsR "[]" []]]])

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
