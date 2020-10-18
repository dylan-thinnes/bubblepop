{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Experiment.Data where

import Data.Functor.Classes (Show1(..))

data Fixity = Infix | Prefix -- | Postfix | Mixfix
    deriving (Show)

type HoAlg (f :: BaseHoF k) (rec :: HoF k)
  = forall (tag :: k). f rec tag -> rec tag

class HFunctor f where
    hmap :: (forall anytag. r anytag -> r' anytag)
         -> f r tag -> f r' tag

instance HFunctor (ExprF passes) where
    hmap _ (VarF str)                 = VarF str
    hmap f (IfF bool true false)      = IfF (f bool) (f true) (f false)
    hmap f (AppF fixity function arg) = AppF fixity (f function) (f arg)
    hmap _ (LitNumF dbl)              = LitNumF dbl
    hmap f (AnyExprF exp)             = AnyExprF (f exp)

cata :: forall f tag rec
     . (HFunctor f)
     => HoAlg f rec -> HFix f tag -> rec tag
cata algebra (HIn x) =
    algebra (hmap (cata algebra) x)

-- Tags for tree types and constructors
data DataTag = ExprT ExprTag | TypeT TypeTag
data ExprTag = VarT | IfT | AppT | LitNumT | AnyExprT
data TypeTag = ForallT | TyAppT | ConcreteT | BoundT

-- Quantified, Fixpointed, Annotated, Summed, and Pattern-Matched combination
-- of Expr & Type into one syntax tree
type TreeF = Sums [ExprF, TypeF]
newtype Tree passes = Tree (Quant (Everything passes TreeF))
type Everything passes f = HFix (Annotated passes f)
pattern Unwrap annots value = HIn (Annotated annots value)

-- Match out expressions
pattern ExprPat annots expr = Unwrap annots (InL expr)

pattern Var     annots name            = ExprPat annots (VarF name)
pattern If      annots bool true false = ExprPat annots (IfF bool true false)
pattern App     annots fixity fun arg  = ExprPat annots (AppF fixity fun arg)
pattern LitNum  annots value           = ExprPat annots (LitNumF value)
pattern AnyExpr annots expr            = ExprPat annots (AnyExprF expr)

-- Match out types
pattern TypePat annots type_ = Unwrap annots (InL (InR type_))

pattern Forall   annots args           = TypePat annots (ForallF args)
pattern TyApp    annots fixity fun arg = TypePat annots (TyAppF fixity fun arg)
pattern Concrete annots name           = TypePat annots (ConcreteF name)
pattern Bound    annots name           = TypePat annots (BoundF name)

-- The base higher-order functor for expressions, ExprF
data ExprF :: [Pass a] -> (DataTag -> *) -> DataTag -> * where
    VarF
        :: String
        -> ExprF passes rec (ExprT VarT)
    IfF
        :: rec (ExprT AnyExprT) -> rec (ExprT AnyExprT) -> rec (ExprT AnyExprT)
        -> ExprF passes rec (ExprT IfT)
    AppF
        :: Fixity
        -> rec (ExprT AnyExprT) -> rec (ExprT AnyExprT)
        -> ExprF passes rec (ExprT AppT)
    LitNumF
        :: Double
        -> ExprF passes rec (ExprT LitNumT)
    AnyExprF
        :: rec (ExprT any)
        -> ExprF passes rec (ExprT AnyExprT)

deriving instance (forall any. Show (rec (ExprT any))) => Show (ExprF passes rec (ExprT AnyExprT))

-- The base higher-order functor for types, TypeF
data TypeF :: [Pass a] -> (DataTag -> *) -> DataTag -> * where
    ForallF
        :: [String]
        -> TypeF passes rec (TypeT ForallT)
    TyAppF
        :: Fixity
        -> TypeF passes rec (TypeT function) -> TypeF passes rec (TypeT argument)
        -> TypeF passes rec (TypeT TyAppT)
    ConcreteF
        :: String
        -> TypeF passes rec (TypeT ConcreteT)
    BoundF
        :: String
        -> TypeF passes rec (TypeT BoundT)

-- Annotation / compiler passes
data Pass a = Parsing | TypeInference | Custom a

-- Applied from Parsing stage:
data Offset = Offset Int | Phantom

-- Applied from TypeInference stage:
data Type

-- Annotation families, ala "Trees That Grow"
type family Annots (tag :: DataTag) (passes :: [Pass a]) where
    Annots e '[] = '[]
    Annots e (x ': xs) = (Annot e x ': Annots e xs)

type family Annot (e :: DataTag) (pass :: Pass a) :: * where
    Annot e Parsing = Offset
    Annot e TypeInference = Type
    Annot e (Custom a) = a

data Annotated (passes :: [Pass a]) f rec tag
    = Annotated
        { annot :: HList (Annots tag passes)
        , branch :: f passes rec tag
        }

deriving instance (Show (f passes rec tag), Show (HList (Annots tag passes))) => Show (Annotated passes f rec tag)

-- Heterogeneous list
-- Take Type-Level Lists to Value-Level Tuples
data HList :: [*] -> * where
    HNil :: HList '[]
    (:>) :: x -> HList xs -> HList (x ': xs)

pattern HEnd x = x :> HNil
pattern x ::> y = x :> HEnd y

instance Show (HList '[]) where
    show _ = "HNil"

instance (Show (HList xs), Show x) => Show (HList (x ': xs)) where
    show (x :> xs) = show x ++ " ': " ++ show xs

-- Kind-level helper synonyms for Higher-order-Functors
type HoF k = k -> *
type BaseHoF k = HoF k -> HoF k
type PassHoF passes k = passes -> HoF k -> HoF k

-- Quantify the argument to a higher-order functor
data Quant f = forall k. Quant { dequant :: f k }

-- Summing over higher-order functors
data Sum (f :: PassHoF p k) (g :: PassHoF p k) (passes :: p) (rec :: HoF k) (a :: k)
    = InL (f passes rec a)
    | InR (g passes rec a)

-- The void higher-order functor, for tying off sums
data VoidHoF :: PassHoF passes k

-- Type family Annot (e :: DataTag) (pass :: Pass a) :: * where
type family Sums (functors :: [PassHoF p k]) :: PassHoF p k where
    Sums '[] = VoidHoF
    Sums (f ': gs) = Sum f (Sums gs)

instance (Show1 (f passes rec), Show1 (g passes rec)) => Show1 (Sum f g passes rec) where
    liftShowsPrec sp arr d x
      = showParen (d > 10) $ showString label . showChar ' ' . sub
        where
            label = case x of
                        InL _ -> "InL"
                        InR _ -> "InR"
            sub = case x of
                    InL f -> liftShowsPrec sp arr d f
                    InR g -> liftShowsPrec sp arr d g

instance Show1 (VoidHoF passes rec) where
    liftShowsPrec _ _ _ _ = showString "VoidHoF"

-- instance (forall f. Show1 f => Show1 (hf f)) => Show1 (HFix hf) where
--     liftShowsPrec sp arr d (HIn out)
--       = showParen (d > 10)
--       $ showString "HIn" . showChar ' ' . liftShowsPrec sp arr 11 out

algAnn :: (f passes rec tag -> rec tag)
       -> Annotated passes f rec tag -> rec tag
algAnn algebra (Annotated { branch }) = algebra branch

algSum :: (f passes rec tag -> rec tag)
       -> (g passes rec tag -> rec tag)
       -> Sum f g passes rec tag -> rec tag
algSum algebra _ (InL left) = algebra left
algSum _ algebra (InR right) = algebra right

-- Fix the base higher-order functor into its recursive tree
data HFix (hf :: BaseHoF k) (a :: k)
    = HIn { hout :: hf (HFix hf) a }

instance (forall f. Show1 f => Show1 (hf f)) => Show1 (HFix hf) where
    liftShowsPrec sp arr d (HIn out)
      = showParen (d > 10)
      $ showString "HIn" . showChar ' ' . liftShowsPrec sp arr 11 out

-- TESTING
newtype Recursor e = Recursor { derec :: [String] }
    deriving (Show)

rebind :: Recursor a -> Recursor b
rebind = Recursor . derec

instance Semigroup (Recursor e) where
    (derec -> a) <> (derec -> b) = Recursor $ a ++ b
instance Monoid (Recursor e) where
    mempty = Recursor []

allExprNames :: ExprF passes Recursor tag -> Recursor tag
allExprNames = \case
   VarF name -> Recursor [name]
   IfF (rebind -> bool) (rebind -> true) (rebind -> false) -> bool <> true <> false
   AppF _ (rebind -> func) (rebind -> arg) -> func <> arg
   LitNumF _ -> Recursor []
   AnyExprF (rebind -> e) -> e

allNames :: Annotated passes TreeF Recursor tag -> Recursor tag
allNames = algAnn $ algSum allExprNames (const $ Recursor [])

--ex1, ex2 :: HFix (ExprF passes) ('ExprT 'IfT)
--ex1
--  = HIn (IfF
--        (HIn $ AnyExprF $ HIn $ VarF "hello")
--        (HIn $ AnyExprF $ HIn $ VarF "hello")
--        (HIn $ AnyExprF $ HIn $ VarF "hello"))
--ex2
--  = HIn (IfF
--        (HIn $ AnyExprF $ HIn (AppF Prefix
--            (HIn $ AnyExprF $ HIn $ VarF "positive")
--            (HIn $ AnyExprF $ HIn $ VarF "x")))
--        (HIn $ AnyExprF $ HIn $ AnyExprF $ HIn $ VarF "posVal")
--        (HIn $ AnyExprF $ HIn $ AnyExprF $ HIn $ VarF "negVal"))
--
--ex3 :: HFix (Annotated '[] TreeF) ('ExprT 'IfT)
--ex3
--  = If HNil
--        (App HNil Prefix
--            (App HNil Prefix
--                (Var HNil ">")
--                (Var HNil "a"))
--            (Var HNil "b"))
--        (App HNil Prefix
--            (App HNil Prefix
--                (Var HNil "-")
--                (Var HNil "a"))
--            (Var HNil "b"))
--        (App HNil Prefix
--            (App HNil Prefix
--                (Var HNil "-")
--                (Var HNil "b"))
--            (Var HNil "a"))
--
