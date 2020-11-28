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

module Experiment.Carrier where

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
import Data.Fix (Fix(..))

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
replace (name, replacement) = cata f
    where
        f :: ExprF Expr -> Expr
        f v = Fix $
            case v of
              Pair (VarF varName) Nothing
                | varName == name -> Pair (VarF varName) (Just replacement)
                | otherwise       -> Pair (VarF varName) Nothing
              y -> y

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

-- Condemn a glorious Expr, casting it back into a RawExpr
condemn :: Expr -> RawExpr
condemn = cata (\(Pair raw hatch) -> embed raw)

-- Glorify2
glorify2 :: RawExpr -> (Env -> Expr)
glorify2 raw env = cata f raw env id
    where
        setListIndex :: [a] -> Int -> a -> [a]
        setListIndex xs i a = zipWith (\j x -> if i == j then a else x) [0..] xs

        f :: RawExprF (Env -> (Expr -> Expr) -> Expr)
          -> Env -> (Expr -> Expr) -> Expr
        f (LitF lit) env cont = Fix $ Pair (LitF lit) Nothing
        f (PrimOpF op) env cont = Fix $ Pair (PrimOpF op) Nothing
        f (IfF cond true false) env cont =
            let construct cond true false =
                    Fix $ Pair (IfF cond true false)
                        $ case cond of -- Escape hatch if boolean's condition is fully evaluated to Lit Bool, will want to check Lit <nonbool>
                            (Fix (Pair (LitF (Bool True)) _))  -> Just $ cont true
                            (Fix (Pair (LitF (Bool False)) _)) -> Just $ cont false
                            _                                  -> Nothing
                cond'  = cond env (\e -> construct e true' false')
                true'  = true env (\e -> construct cond' e false')
                false' = false env (\e -> construct cond' true' e)
             in construct cond' true' false'
        f (LetF name bound body) env cont =
            let construct name bound body =
                    Fix $ Pair (LetF name bound body)
                        $ Just $ cont body -- Escape hatch at any point by substituting in the body - will need further logic when patterns are implemented
                bound' = bound env' (\e -> construct name e body')
                body' = body env' (\e -> construct name bound' e)
                env' = set name bound' env
             in construct name bound' body'
        f (AbsF args body) env cont =
            let construct args body =
                    Fix $ Pair (AbsF args body)
                        $ if null args
                             then Just $ cont body -- Escape hatch if lambda has no remaining arguments, will become useful when AppF becomes curried/partial-aware
                             else Nothing
                env' = foldr remove env args
                body' = body env' (\e -> construct args e)
             in construct args body'
        f (VarF name) env cont =
            Fix $ Pair (VarF name)
                $ cont <$> get env name -- Variables have escape hatches when defined in the environment
        f (AppF func args) env cont =
            let construct func args =
                    Fix $ Pair (AppF func args)
                        $ cont
                        <$> case func of
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
                func' = func env (\e -> construct e args')
                args' = zipWith constructArg [0..] args
                constructArg index arg = arg env (\e -> construct func' (setListIndex args' index e))
             in construct func' args'

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
        f (AbsF args body) = ("\\" ++ unwords args) <| indent body
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
    print expr
    putStrLn $ prettyRaw $ condemn expr
    let options = crumbs expr
    if null options then pure expr
        else do
            mapM_ (uncurry showOption) (zip [0..] options)
            i <- readLn
            let crumb = options !! i
            case hansel expr crumb of
              Left err -> (putStrLn $ "Error: " ++ err) >> repl expr
              Right newExpr -> repl newExpr
    where
        showOption i option = putStr (show i ++ ": ") >> print option

repl2 :: Expr -> IO Expr
repl2 e = do
    putStrLn $ prettyRaw $ condemn e
    let options = crumbs e
    if null options then pure e
        else do
            mapM_ (uncurry showOption) (zip [0..] options)
            i <- readLn
            let crumb = options !! i
            case gretel e crumb of
              Left err -> (putStrLn $ "Error: " ++ err) >> repl2 e
              Right e -> repl2 e
    where
        showOption i option = putStr (show i ++ ": ") >> print option

-- Example
ex_simple :: RawExpr
ex_simple =
    IfR
        (AppR
            (PrimOpR $ PrimOp "<" [TInt, TInt] (\[Int i, Int j] -> Bool $ i < j))
            [ (AppR
                (PrimOpR $ PrimOp "*" [TInt, TInt] (\[Int i, Int j] -> Int $ i * j))
                [ VarR "x"
                , LitR (Int 2)
                ])
            , (AppR
                (PrimOpR $ PrimOp "*" [TInt, TInt] (\[Int i, Int j] -> Int $ i * j))
                [ LitR (Int 5)
                , LitR (Int 7)
                ])
            ])
        (VarR "x")
        (VarR "y")

ex_fix :: RawExpr
ex_fix =
    LetR "x" (AppR (VarR "f") [VarR "x"]) (VarR "x")
