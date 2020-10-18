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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-unused-matches #-}

module Experiment.PatternsWOReplaceLet where

import qualified Data.Map as M
import Data.Map (Map, (!?), insert, fromList, delete)
import Data.Fix (Fix(..))
import Data.Functor.Foldable hiding (Cons)
import Text.Show.Deriving
import Data.Functor.Classes
import Data.Functor.Product
import Data.Functor.Compose
import Control.Monad (join, guard)
import Control.Monad.Free
import qualified Data.List.NonEmpty as N
import Data.List.NonEmpty (NonEmpty(..), (<|))
import Data.Functor ((<&>))
import Debug.Trace
import Control.Applicative ((<|>))
import GHC.Exts
import Data.Foldable
import Data.Maybe (mapMaybe)

data PrimOp = PrimOp
    { primOpName :: String
    , primOpContract :: [LiteralType]
    , primOpFunc :: [Literal] -> Literal
    }
instance Show PrimOp where
    show (PrimOp name _ _) = name

-- EXPRESSIONS
-- expressions without behaviour
type RawExpr = Fix RawExprF

data RawExprF a
    = LitF Literal
    | AppF a [a]
    | AbsF [String] a
    | VarF String
    | IfF  a a a
    | EConsF (Cons a)
    | CaseF a [(Pattern String, a)]
    | LetF String a a
    | PrimOpF PrimOp
    deriving (Functor, Foldable, Traversable)

data Cons a = Cons String [a]
    deriving (Show, Functor, Foldable, Traversable)

data Pattern a
    = PCons (Cons (Pattern a))
    | PWildcard
    | PLiteral Literal
    | PEscape a
    deriving (Show, Functor, Foldable, Traversable)

prettyPat :: Pattern String -> String
prettyPat (PCons (Cons name args)) = name ++ " " ++ unwords (prettyPat <$> args)
prettyPat PWildcard = "_"
prettyPat (PLiteral lit) = prettyLit lit
prettyPat (PEscape a) = a

instance IsString (Pattern String) where
    fromString = PEscape

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

deriveShow1 ''Cons
deriveShow1 ''RawExprF

pattern LitR lit = Fix (LitF lit)
pattern AppR fun args = Fix (AppF fun args)
pattern AbsR args body = Fix (AbsF args body)
pattern VarR name = Fix (VarF name)
pattern IfR cond true false = Fix (IfF cond true false)
pattern LetR name bound body = Fix (LetF name bound body)
pattern EConsR name args = Fix (EConsF (Cons name args))
pattern CaseR scrut branches = Fix (CaseF scrut branches)
pattern PrimOpR prim = Fix (PrimOpF prim)

pattern LitG hatch lit             = Fix (Pair (LitF lit)             hatch)
pattern AppG hatch fun args        = Fix (Pair (AppF fun args)        hatch)
pattern AbsG hatch args body       = Fix (Pair (AbsF args body)       hatch)
pattern VarG hatch name            = Fix (Pair (VarF name)            hatch)
pattern IfG hatch cond true false  = Fix (Pair (IfF cond true false)  hatch)
pattern LetG hatch name bound body = Fix (Pair (LetF name bound body) hatch)
pattern EConsG hatch cons          = Fix (Pair (EConsF cons)          hatch)
pattern CaseG hatch scrut branches = Fix (Pair (CaseF scrut branches) hatch)
pattern PrimOpG hatch prim         = Fix (Pair (PrimOpF prim)         hatch)

toLit :: Expr -> Maybe Literal
toLit (Fix (Pair (LitF lit) _)) = Just lit
toLit _ = Nothing

patternNames :: Pattern a -> [a]
patternNames = Data.Foldable.toList

matchPat :: Pattern String -> Expr -> Maybe [(String, Expr)]
matchPat (PCons (Cons consFormal formals)) (EConsG _ (Cons consReal reals))
    = do
        guard $ consFormal == consReal
        guard $ length formals == length reals
        matchings <- sequence $ zipWith matchPat formals reals
        pure $ concat matchings
matchPat PWildcard expr = Just []
matchPat (PLiteral formal) (LitG _ real) = guard (formal == real) >> pure []
matchPat (PEscape formal) real = pure $ [(formal, real)]
matchPat _ _ = Nothing

data Crumb
    = AppFunc | AppArg Int
    | AbsBody
    | IfCond | IfTrue | IfFalse
    | LetBound -- | LetBody
    | EConsArg Int
    | CaseBody | CaseBranch Int
    deriving (Show)

type Crumbtrail = [Crumb]

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

-- Expressions with environments, and holes
type Expr = Fix ExprF
type ExprF = Product RawExprF Maybe

crumbs :: Expr -> [Crumbtrail]
crumbs = cata f
    where
        f :: ExprF [Crumbtrail] -> [Crumbtrail]
        f (Pair expr hatch) = g expr <> h hatch

        g :: RawExprF [Crumbtrail] -> [Crumbtrail]
        g (LitF lit) = []
        g (PrimOpF op) = []
        g (VarF name) = []
        g (AppF fun args) = ((AppFunc :) <$> fun) <> join (zipWith (fmap . (:)) (map AppArg [0..]) args)
        g (AbsF names body) = (AbsBody :) <$> body
        g (IfF cond true false) = join $ zipWith (fmap . (:)) [IfCond, IfTrue, IfFalse] [cond, true, false]
        g (LetF name bound body) = ((LetBound :) <$> bound) -- <> ((LetBody :) <$> body)
        g (EConsF (Cons _ args)) = join (zipWith (fmap . (:)) (map EConsArg [0..]) args)
        g (CaseF body branches) = ((CaseBody :) <$> body) <> join (zipWith (fmap . (:)) (map CaseBranch [0..]) (fmap snd branches))

        h :: Maybe a -> [Crumbtrail]
        h Nothing = []
        h (Just _) = [[]]

-- ENVIRONMENTS
newtype Env = Env { unenv :: Map String Expr }
deriving instance Show Expr => Show Env

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
            let unchanged = fst <$> v
                changed = snd <$> v
            in
            case v of
              Pair (VarF varName) Nothing
                | name == varName -> replacement
                | otherwise       -> Fix $ Pair (VarF varName) Nothing
              Pair (LetF letName _ _) _
                | name == letName -> embed unchanged
                | otherwise       -> embed changed
              Pair (AbsF names _) _
                | name `elem` names -> embed unchanged
                | otherwise         -> embed changed
              Pair (CaseF scrutee branches) hatch
                -> CaseG (snd <$> hatch) (snd scrutee) 
                    $ branches <&> \(pat, body)
                                    -> ( pat
                                       , if name `elem` patternNames pat
                                           then fst body
                                           else snd body
                                       )
              _ -> embed changed


-- Glorify a RawExpr into a glorious Expr, by binding environments and attaching escape hatches
glorify :: RawExpr -> (Env -> Expr)
glorify = cata f
    where
        f :: RawExprF (Env -> Expr) -> (Env -> Expr)
        f expr env = Fix $ memo env $ modifyEnv expr env

        memo :: Env -> RawExprF Expr -> ExprF Expr
        memo env x = Pair x (hatch env x)

        modifyEnv :: RawExprF (Env -> Expr) -> Env -> RawExprF Expr
        modifyEnv (LetF name expr body) env = LetF name expr' (body env')
            where
                env' = set name expr' env
                expr' = expr env'
        modifyEnv (AbsF names body)     env = AbsF names $ body $ foldr remove env names
        modifyEnv (CaseF scrutee branches) env = CaseF (scrutee env) (map handleBranch branches)
            where
                handleBranch (pat, branch) = (pat, branch $ foldr remove env (patternNames pat))
        modifyEnv f                     env = ($ env) <$> f

        hatch :: Env -> RawExprF Expr -> Maybe Expr
        hatch _ (LitF _)    = Nothing -- Literals have no escape hatches
        hatch _ (PrimOpF _) = Nothing -- PrimOps have no escape hatches
        hatch _ (EConsF _)  = Nothing -- Constructors have no escape hatches
        hatch e (VarF name) = get e name -- Variables have escape hatches when defined in the environment
        hatch _ (IfF cond true false) =
            case cond of
              (Fix (Pair (LitF (Bool True)) _))  -> Just true
              (Fix (Pair (LitF (Bool False)) _)) -> Just false
              _                                  -> Nothing
        hatch _ (AppF func args) =
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
        hatch _ (AbsF args body) = -- Escape hatch if lambda has no remaining arguments, will become useful when AppF becomes curried/partial-aware
            if null args then Just body else Nothing
        hatch _ (LetF name expr body) = -- Escape hatch at any point by substituting in the body - will need further logic when patterns are implemented
            Just $ replace (name, expr) body
        hatch _ (CaseF scrutee branches) = -- Escape hatch when a pattern matches the scrutee
            let f [] = Nothing
                f ((pat, body):rest) =
                    case matchPat pat scrutee of
                      Nothing -> f rest
                      Just replacements -> Just $ foldr replace body replacements
             in f branches

reglorify :: Expr -> Expr
reglorify = cata (\(Pair e k) -> Fix $ Pair e (rehatch k e))
    where
        rehatch :: Maybe Expr -> RawExprF Expr -> Maybe Expr
        rehatch e (LitF _)    = Nothing -- Literals have no escape hatches
        rehatch e (PrimOpF _) = Nothing -- PrimOps have no escape hatches
        rehatch e (EConsF _)  = Nothing -- Constructors have no escape hatches
        rehatch e (VarF name) = e -- Variables have escape hatches when defined in the environment, not when rehatching
        rehatch e (IfF cond true false) =
            case cond of
              (Fix (Pair (LitF (Bool True)) _))  -> Just true
              (Fix (Pair (LitF (Bool False)) _)) -> Just false
              _                                  -> Nothing
        rehatch e (AppF func args) =
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
        rehatch e (AbsF args body) = -- Escape hatch if lambda has no remaining arguments, will become useful when AppF becomes curried/partial-aware
            if null args then Just body else Nothing
        rehatch e (LetF name expr body) = -- Escape hatch at any point by substituting in the body - will need further logic when patterns are implemented
            Just $ replace (name, expr) body
        rehatch e (CaseF scrutee branches) = -- Escape hatch when a pattern matches the scrutee
            let f [] = Nothing
                f ((pat, body):rest) =
                    case matchPat pat scrutee of
                      Nothing -> f rest
                      Just replacements -> Just $ foldr replace body replacements
             in f branches

-- Condemn a glorious Expr, casting it back into a RawExpr
condemn :: Expr -> RawExpr
condemn = cata (\(Pair raw hatch) -> embed raw)

prettyRaw :: RawExpr -> String
prettyRaw = unlines . N.toList . cata f
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
        parenthesize (line :| []) = ("(" ++ line ++ ")") :| []
        parenthesize (line :| xs) = ("(" ++ line) :| (init xs ++ [last xs ++ ")"])

        f :: RawExprF (NonEmpty String) -> NonEmpty String
        f (LitF lit) = line $ prettyLit lit
        f (AppF body args) = body <> indent (nec args)
        f (AbsF args body) = parenthesize $ ("\\" ++ unwords args ++ " ->") <| indent body
        f (VarF name) = line name
        f (IfF cond true false) = line "if" <> indent cond <> line "then" <> indent true <> line "else" <> indent false
        f (PrimOpF op) = line $ show op
        f (LetF name bound body) = line ("let " ++ name ++ " =") <> indent bound <> line "in" <> indent body
        f (EConsF (Cons name args)) = parenthesize $ nec' name (indent <$> args)
        f (CaseF scrutee branches) = line "case" <> indent (parenthesize scrutee <> nec' "of" (f <$> branches))
            where
                f (pat, body) = line (prettyPat pat) <> indent (line "->" <> body)

pretty :: Either String Expr -> IO ()
pretty = \case
    Left e -> putStrLn $ "Error: " ++ e
    Right e -> putStrLn $ prettyRaw $ condemn e

repl :: String -> Expr -> IO Expr
repl str expr = do
    putStr "\ESC[2J\ESC[H"
    putStrLn "============================================"
    putStrLn str
    putStrLn $ prettyRaw $ condemn expr
    let options = crumbs expr
    if null options then pure expr
        else do
            mapM_ (uncurry showOption) (zip [0..] options)
            i <- readLn
            if | i < 0 -> pure expr
               | i > length options -> repl "Error: Option index out of bounds." expr
               | otherwise -> do
                    let crumb = options !! i
                    case hansel expr crumb of
                      Left err -> repl ("Error: " ++ err) expr
                      Right newExpr -> repl "Success." $ reglorify newExpr
    where
        showOption i option = putStr (show i ++ ": ") >> print option

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

ex_simple' = glorify ex_simple env

ex_fix :: RawExpr
ex_fix =
    LetR "x" (AppR (VarR "f") [VarR "x"]) (VarR "x")

ex_fix' = glorify ex_fix env

ex_lambda :: RawExpr
ex_lambda =
    LetR "plusTwo"
        (AbsR ["y"] (AppR primPlus [LitR (Int 2), (VarR "y")]))
        (AppR primTimes [AppR (VarR "plusTwo") [VarR "x"], LitR (Int 3)])

ex_lambda' = glorify ex_lambda env

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

ex_fac' = glorify ex_fac env

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
        (AppR (VarR "foldr") [primPlus, LitR (Int 1), EConsR ":" [LitR (Int 2), EConsR ":" [LitR (Int 3), EConsR "[]" []]]])

ex_foldr' = glorify ex_foldr env
