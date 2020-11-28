{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE NoStarIsType      #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}
module Bubble.GHC.Expr where

import           Bubble.GHC.Classes
import           Bubble.GHC.Utils

import           Control.Monad              (guard, join)
import           Control.Monad.State        hiding (lift)
import           Data.Functor.Const
import           Data.Functor.Foldable
import           Data.Functor.Product
import           Data.Functor.Sum
import           Data.Word
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax

import           Text.Show.Deriving

-- Redices
newtype Redex a = R { unR :: Maybe a }
    deriving (Show, Functor, Foldable, Traversable)

pattern Redex a = R (Just a)
pattern NoRedex = R Nothing

maybeToRedex :: Maybe a -> Redex a
maybeToRedex = R

deriveShow1 ''Redex

-- Primitive operations
data PrimOp = PrimOp
    { primOpName     :: Name
    , primOpContract :: [LitContractType]
    , primOpFunc     :: [Lit] -> Lit
    }

data LitContractType = Char
    | String
    | Integer
    | Rational

matchLitContract :: Functor f => LitContractType -> ExpG f -> Maybe Lit
matchLitContract contract expr =
    case (contract, condemn expr) of
        (Char,     LitE lit@(CharL _))     -> Just lit
        (String,   LitE lit@(StringL _))   -> Just lit
        (Integer,  LitE lit@(IntegerL _))  -> Just lit
        (Rational, LitE lit@(RationalL _)) -> Just lit
        _                                  -> Nothing

instance Show PrimOp where
    show (PrimOp name _ _) = show name

type Exception = String

-- Infix versions of Sum and Product
type (*) a b = Product a b
type (+) a b = Sum a b

type P3 f g h = f * g * h
pattern P3 a b c = a `Pair` b `Pair` c
type S3 f g h = f + g + h
pattern S31 a = InL (InL a)
pattern S32 b = InL (InR b)
pattern S33 c = InR c

type ExpG f = Fix (ExpGF f)
type ExpGF f = P3 (S3 ExpF (Const PrimOp) (Const Exception)) (Const Int) f
pattern FE  id hatch expr   = Fix (FEF id hatch expr)
pattern FP  id hatch primop = Fix (FPF id hatch primop)
pattern FX  id hatch except = Fix (FXF id hatch except)
pattern FA  id hatch any    = Fix (FAF id hatch any)
pattern FEF id hatch expr   = P3 (ExprE expr)        (Const id) hatch
pattern FPF id hatch primop = P3 (PrimOpE primop)    (Const id) hatch
pattern FXF id hatch except = P3 (ExceptionE except) (Const id) hatch
pattern FAF id hatch any    = P3 any                 (Const id) hatch
pattern ExprE expr   = S31 expr
pattern PrimOpE prim = S32 (Const prim)
pattern ExceptionE x = S33 (Const x)

commend :: Exp -> ExpG Redex
commend exp = evalState (cata f exp) 0
    where
        f :: ExpF (State Int (ExpG Redex)) -> State Int (ExpG Redex)
        f expf = do
            id <- get
            modify succ
            expf' <- sequence expf
            pure $ FE id NoRedex expf'

condemn :: Functor f => ExpG f -> Exp
condemn = cata
        $ \(FAF _ _ exprOrPrim) ->
            case exprOrPrim of
                ExprE expr            -> embed expr
                PrimOpE (PrimOp {..}) -> VarE primOpName
                ExceptionE exception  ->
                    AppE
                        (VarE (Name (OccName "error") (NameG VarName (PkgName "base") (ModName "GHC.Err"))))
                        (LitE $ StringL exception)

matchPat :: Pat -> ExpG f -> Maybe [(Name, ExpG f)]
matchPat (LitP lit1) (FE _ _ (LitEF lit2)) = do
    guard (lit1 == lit2)
    Just []
matchPat (VarP name) e = Just [(name, e)]
matchPat (TupP pats) (FE _ _ (TupEF exps)) = do
    guard (length pats == length exps)
    submatches <- sequence $ zipWith matchPat pats exps
    Just $ concat submatches
matchPat (ConP name1 argPats) expr =
    case expr of
      FE _ _ (ConEF name2) -> do
          guard (name1 == name2)
          Just []
      FE _ _ (AppEF func arg) -> do
          guard $ length argPats > 0
          funcMatch <- matchPat (ConP name1 $ init argPats) func
          lastArgMatch <- matchPat (last argPats) arg
          Just $ funcMatch ++ lastArgMatch
matchPat WildP _ = Just []
matchPat _ _ = Nothing -- error "Can't match _ against _"

replace :: (Name, ExpG Redex) -> ExpG Redex -> ExpG Redex
replace (name, value) body = para f body
    where
        f e@(FEF _ _ (VarEF n)) =
            if name == n
               then value
               else embed $ fmap fst e
        f e@(FEF _ _ (LamEF pats body)) =
            undefined
            --if name `elem` foldMap definesNames pats
            --   then embed $ fmap fst e
            --   else embed $ fmap snd e
        -- TODO: handle let & case statement
        f e = embed $ fmap snd e

class DefinesNames a where
    definesNames :: a -> Maybe [Name]

instance DefinesNames (ExpF a) where
    definesNames (LamEF pats _)  = undefined --Just $ foldMap definesNames pats
    definesNames (LetEF decls _) = undefined --Just $ foldMap (definesNames . project) decls
    definesNames _               = Nothing

instance DefinesNames Pat where
    definesNames = undefined --cata f
        where
            f (VarPF name) = [name]
            f pat          = foldMap id pat

instance DefinesNames (DecF a) where
    definesNames (FunDF name _) = Just [name]
    definesNames (FunDF name _) = Just [name]

define :: (Name, ExpG Redex) -> ExpG Redex -> ExpG Redex
define (name, value) body = para f body
    where
        f e@(FEF id redex (VarEF n)) =
            if occName name == occName n
               then FE id (Redex value) (VarEF n)
               else embed $ fmap fst e
        f e@(FEF _ _ (LamEF pats body)) =
            undefined
            --if occName name `elem` map occName (foldMap definesNames pats)
            --   then embed $ fmap fst e
            --   else embed $ fmap snd e
        -- TODO: handle let & case statement
        f e = embed $ fmap snd e

--rerefine :: ExpG Redex -> ExpG Redex
--rerefine = cata ()

hatchAll :: ExpG Redex -> ExpG Redex
hatchAll = cata f
    where
    f gexprf@(FAF id redex exprf) =
        let newRedex = hatch $ embed gexprf
         in FA id newRedex exprf

hatch :: ExpG Redex -> Redex (ExpG Redex)
hatch expr =
    case expr of
        FP _ _ (PrimOp _ _ _) -> NoRedex
        FE _ _ (LitEF _) -> NoRedex
        FE _ r (VarEF name) -> r
        FE _ _ (ConEF name) -> NoRedex
        FE _ _ (ParensEF expr) -> NoRedex
        FE _ _ (CondEF cond true false) ->
            case cond of
                FE _ _ (ConEF (Name (OccName name) flavour))
                  | name == "True" -> Redex true
                  | name == "False" -> Redex false
                _ -> NoRedex
        FE _ _ (AppEF func arg) ->
            case func of
                FE i _ (LamEF (pat:pats) body) -> R $ do
                    nameExpPairs <- matchPat pat func
                    let newBody = foldr replace body nameExpPairs
                    Just $ if length pats == 0
                           then newBody
                           else FE i NoRedex (LamEF pats newBody)
                FP i _ (PrimOp {..}) -> R $ do
                    --lits <- sequence $ zipWith matchLitContract primOpContract undefined
                    undefined
                    --nameExpPairs <- matchPat pat func
                    --let newBody = foldr replace body nameExpPairs
                    --Just $ if length pats == 0
                    --       then newBody
                    --       else FE i NoRedex (LamEF pats newBody)
                _ -> NoRedex
        FE _ _ (InfixEF ml op mr) ->
            case (ml, mr) of
                (Just l, Just r) ->
                    case op of
                        FE redex id (LamEF [patL,patR] body) -> R $ do
                            nameExpPairs1 <- matchPat patL l
                            nameExpPairs2 <- matchPat patR r
                            let newBody = foldr replace body (nameExpPairs1 <> nameExpPairs2)
                            Just newBody
                        FP i _ (PrimOp {..}) -> R $ do
                            let args = [l, r]
                            guard $ length primOpContract == length args
                            lits <- sequence $ zipWith matchLitContract primOpContract args
                            Just $ FE (-1) NoRedex $ LitEF $ primOpFunc lits
                        _ -> NoRedex
                _ -> NoRedex
        FE _ _ (LetEF decls expression) ->
            undefined
        _ -> NoRedex

eat :: Int -> ExpG Redex -> ExpG Redex
eat target = cata f
    where
        f x@(FAF id redex _) =
            case redex of
              Redex out
                | id == target -> out
              _ -> embed x

collect :: ExpG Redex -> [Int]
collect = cata f
    where
        f (FAF id redex children) = self <> concat children
            where
                self = case redex of
                         NoRedex -> []
                         Redex _ -> [id]
