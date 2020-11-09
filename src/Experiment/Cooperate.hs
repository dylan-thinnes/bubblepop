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

module Experiment.Cooperate where

import qualified Data.Map as M
import Data.Map (Map, (!?), insert, fromList, delete)
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
    | LetF String a a
    | PrimOpF PrimOp
    deriving (Functor, Foldable, Traversable)

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

deriveShow1 ''RawExprF

pattern LitR lit = Fix (LitF lit)
pattern AppR fun args = Fix (AppF fun args)
pattern AbsR args body = Fix (AbsF args body)
pattern VarR name = Fix (VarF name)
pattern IfR cond true false = Fix (IfF cond true false)
pattern LetR name bound body = Fix (LetF name bound body)
pattern PrimOpR prim = Fix (PrimOpF prim)

toLit :: Expr -> Maybe Literal
toLit (Fix (Pair (LitF lit) _)) = Just lit
toLit _ = Nothing

data Crumb
    = AppFunc | AppArg Int
    | AbsBody
    | IfCond | IfTrue | IfFalse
    | LetBound | LetBody
    deriving (Show)

type Crumbtrail = [Crumb]

gretel :: Expr -> (Crumbtrail -> Either String Expr)
gretel = para f
    where
        f :: ExprF (Expr, Crumbtrail -> Either String Expr) -> Crumbtrail -> Either String Expr
        f (Pair expr hatch) trail =
            case trail of
              [] -> case hatch of
                      Just replacement -> Right $ fst replacement
                      Nothing -> Left "Tried to take a nonexistent escape hatch!"
              (crumb:rest)
                 -> case (snd <$> expr, crumb) of
                      (AppF func _,    AppFunc)  -> func rest
                      (AppF _ args,    AppArg i) ->
                          if i < length args
                             then (args !! i) rest
                             else Left $ "Tried to follow a crumb to a nonexistent function argument, " ++ show (length args) ++ " " ++ show i
                      (AbsF _ body,    AbsBody)  -> body rest
                      (IfF cond _ _,   IfCond)   -> cond rest
                      (IfF _ true _,   IfTrue)   -> true rest
                      (IfF _ _ false,  IfFalse)  -> false rest
                      (LetF _ bound _, LetBound) -> bound rest
                      (LetF _ _ body,  LetBody)  -> body rest
                      _ -> Left "Incompatible crumb and constructor."

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
                      (LetF n b body,  LetBody)  -> sequence $ LetF n (pure $ fst b) (snd body rest)
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
        g (LetF name bound body) = ((LetBound :) <$> bound) <> ((LetBody :) <$> body)

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

-- COMPLEXITY BUILDS, I KNOW NOT Y
-- THE ABSTRACTIONS MULTIPLY
-- WHATEVER I DO, I CANNOT KEEP THEM AT BAY
-- I CAN FEEL MY MEANING SLIPPING AWAY

-- Simple replace, can't handle name collisions...
replace :: (String, Expr) -> Expr -> Expr
replace (name, replacement) = para f
    where
        f :: ExprF (Expr, Expr) -> Expr
        f v =
            let unchanged = fst <$> v
                changed = snd <$> v
            in
            case changed of
              Pair (VarF varName) Nothing
                | name == varName -> replacement
                | otherwise       -> Fix $ Pair (VarF varName) Nothing
              Pair (LetF letName _ _) _
                | name == letName -> embed unchanged
                | otherwise       -> embed changed
              Pair (AbsF names _) _
                | name `elem` names -> embed unchanged
                | otherwise         -> embed changed
              _ -> embed changed


--bindVars :: RawExprF (Env -> Expr) -> Env -> Expr
--bindVars expr env =
--    let expr' = modifyEnv expr' env
--        env' = ($ env') <$> expr
--     in expr'

-- Glorify a RawExpr into a glorious Expr, by binding environments and attaching escape hatches
glorify :: RawExpr -> (Env -> Expr)
glorify = cata f
    where
        f :: RawExprF (Env -> Expr) -> (Env -> Expr)
        f expr env = Fix $ memo env expr'
            where
                env' = modifyEnv expr' env
                expr' = fmap ($ env') expr

        memo :: Env -> RawExprF Expr -> ExprF Expr
        memo env x = Pair x (hatch env x)

        modifyEnv :: RawExprF Expr -> Env -> Env
        modifyEnv (LetF name expr _) = set name expr
        modifyEnv (AbsF names _)     = \env -> foldr remove env names
        modifyEnv _                  = id

        hatch :: Env -> RawExprF Expr -> Maybe Expr
        hatch _ (LitF _)    = Nothing -- Literals have no escape hatches
        hatch _ (PrimOpF _) = Nothing -- PrimOps have no escape hatches
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
            Just body

reglorify :: Expr -> Expr
reglorify = cata (\(Pair e k) -> Fix $ Pair e (rehatch k e))
    where
        rehatch :: Maybe Expr -> RawExprF Expr -> Maybe Expr
        rehatch e (LitF _)    = Nothing -- Literals have no escape hatches
        rehatch e (PrimOpF _) = Nothing -- PrimOps have no escape hatches
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
            Just body

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

        indent :: NonEmpty String -> NonEmpty String
        indent = fmap ("  " ++)

        f :: RawExprF (NonEmpty String) -> NonEmpty String
        f (LitF (Int i)) = line $ show i
        f (LitF (Char c)) = line $ show c
        f (LitF (String s)) = line $ show s
        f (LitF (Bool b)) = line $ show b
        f (AppF body args) = body <> indent (nec args)
        f (AbsF args body) = ("(\\" ++ unwords args ++ " ->") <| indent (body <> line ")")
        f (VarF name) = line name
        f (IfF cond true false) = line "if" <> indent cond <> line "then" <> indent true <> line "else" <> indent false
        f (PrimOpF op) = line $ show op
        f (LetF name bound body) = line ("let " ++ name ++ " =") <> indent bound <> line "in" <> indent body

pretty :: Either String Expr -> IO ()
pretty = \case
    Left e -> putStrLn $ "Error: " ++ e
    Right e -> putStrLn $ prettyRaw $ condemn e

repl :: Expr -> IO Expr
repl expr = do
    putStr "\ESC[2J\ESC[H"
    putStrLn "============================================"
    putStrLn $ prettyRaw $ condemn expr
    let options = crumbs expr
    if null options then pure expr
        else do
            mapM_ (uncurry showOption) (zip [0..] options)
            i <- readLn
            if i < 0
               then pure expr
               else do
                    let crumb = options !! i
                    case hansel expr crumb of
                      Left err -> (putStrLn $ "Error: " ++ err) >> repl expr
                      Right newExpr -> repl $ reglorify newExpr
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

church_nil :: RawExpr
church_nil = AbsR ["cons", "nil"] (VarR "nil")

church_cons :: RawExpr
church_cons = AbsR ["head", "tail"] $ AbsR ["cons", "nil"] (AppR (VarR "cons") [VarR "head", AppR (VarR "tail") [VarR "cons", VarR "nil"]])

ex_church =
    LetR "nil" church_nil
    $ LetR "cons" church_cons
    $ LetR "list"
        (AppR (VarR "cons") [LitR $ Int 4, AppR (VarR "cons") [LitR $ Int 2, AppR (VarR "cons") [LitR $ Int 3, VarR "nil"]]])
        (AppR (VarR "list") [primTimes, LitR $ Int 1])

ex_church' = glorify ex_church env
