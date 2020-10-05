{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Experiment.Data where

import Experiment.Utils

import Data.Functor.Classes (Show1 (..))

-- instance HFunctor (ExprF passes) where
--     hmap _ (VarF str)                 = VarF str
--     hmap f (IfF bool true false)      = IfF (f bool) (f true) (f false)
--     hmap f (AppF fixity function arg) = AppF fixity (f function) (f arg)
--     hmap _ (LitNumF dbl)              = LitNumF dbl
--     hmap f (AnyExprF exp)             = AnyExprF (f exp)
-- 

-- Quantified, Fixpointed, Annotated, Summed, and Pattern-Matched combination
-- of Expr & Type into one syntax tree
type TreeF = Sums [ExprF, TypeF]
newtype Tree passes tag = Tree (HFix (TreeF (Ann passes)) tag)

-- Match out expressions
pattern ExprPat expr = HIn (InL expr)

pattern Var     growth name            = ExprPat (VarF growth name)
pattern If      growth bool true false = ExprPat (IfF growth bool true false)
pattern App     growth fixity fun arg  = ExprPat (AppF growth fixity fun arg)
pattern LitNum  growth value           = ExprPat (LitNumF growth value)

-- Match out types
pattern TypePat type_ = HIn (InL (InR type_))

pattern Forall   growth args           = TypePat (ForallF growth args)
pattern TyApp    growth fixity fun arg = TypePat (TyAppF growth fixity fun arg)
pattern Concrete growth name           = TypePat (ConcreteF growth name)
pattern Bound    growth name           = TypePat (BoundF growth name)

-- Tags for tree types and constructors
data TreeTag = ExprTree | TypeTree | DeclTree | PattTree | NameTree
data ConsTag = ExprT ExprTag | TypeT TypeTag | DeclT DeclTag | PattT PattTag | NameT NameTag
data ExprTag = VarT | IfT | AppT | LitNumT | AnyExprT
data TypeTag = ForallT | TyAppT | ConcreteT | BoundT
data DeclTag = ModuleT | AssignT | ImportT
data PattTag = PatConsT | BareT
data NameTag = AnyNameT

-- The base higher-order functor for expressions, ExprF
data ExprF :: (ConsTag -> *) -> (TreeTag -> *) -> TreeTag -> * where
    VarF -- Single variable
        :: grow (ExprT VarT)
        -> String -- Variable name
        -> ExprF grow rec ExprTree
    IfF -- If statement
        :: grow (ExprT IfT)
        -> rec ExprTree -- Condition
        -> rec ExprTree -- True body
        -> rec ExprTree -- False body
        -> ExprF grow rec ExprTree
    AppF -- Function application
        :: grow (ExprT AppT)
        -> Fixity
        -> rec ExprTree -- Function
        -> rec ExprTree -- Argument
        -> ExprF grow rec ExprTree
    LitNumF -- Number literal, e.g. 4, 5.6
        :: grow (ExprT LitNumT)
        -> Double -- Literal numeral
        -> ExprF grow rec ExprTree

deriving instance (forall (a :: ConsTag). Show (grow a), forall (b :: TreeTag). Show (rec b))
  => Show (ExprF grow rec tag)

data Fixity
    = Prefix -- E.g. f 2 3, Just True, Maybe Bool
    | Infix -- E.g. 2 + 3, Nothing :*: "Err", Int :+: String
    -- | Postfix | Mixfix -- Not included at the moment
    deriving (Show)

-- The base higher-order functor for types, TypeF
data TypeF :: (ConsTag -> *) -> (TreeTag -> *) -> TreeTag -> * where
    ForallF -- Universal quantification of type variables
        :: grow (TypeT ForallT)
        -> [String]
        -> TypeF grow rec TypeTree
    TyAppF -- Function application, type-level
        :: grow (TypeT TyAppT)
        -> Fixity
        -> TypeF grow rec TypeTree -- Function
        -> TypeF grow rec TypeTree -- Argument
        -> TypeF grow rec TypeTree
    ConcreteF -- Concrete type, e.g. Int
        :: grow (TypeT ConcreteT)
        -> String
        -> TypeF grow rec TypeTree
    BoundF -- Type variable bound by a forall, e.g. a
        :: grow (TypeT BoundT) 
        -> String
        -> TypeF grow rec TypeTree

deriving instance (forall (a :: ConsTag). Show (grow a), forall (b :: TreeTag). Show (rec b))
  => Show (TypeF grow rec tag)

-- The base higher-order functor for declarations, DeclF
data DeclF :: (ConsTag -> *) -> (TreeTag -> *) -> TreeTag -> * where
    ModuleF -- Module header
        :: grow (DeclT ModuleT)
        -> [String] -- Module path
        -> DeclF grow rec DeclTree
    AssignF -- Assignment statement
        :: grow (DeclT AssignT)
        -> String -- Name
        -> [rec PattTree] -- Argument patterns
        -> rec ExprTree -- Body
        -> DeclF grow rec DeclTree
    ImportF -- Import statement
        :: grow (DeclT ImportT)
        -> [String] -- Module path
        -> Bool -- Qualified or not
        -> Maybe String -- as <name>
        -> DeclF grow rec DeclTree

deriving instance (forall (a :: ConsTag). Show (grow a), forall (b :: TreeTag). Show (rec b))
  => Show (DeclF grow rec tag)

-- The base higher-order functor for pattern matching, PattF
data PattF :: (ConsTag -> *) -> (TreeTag -> *) -> TreeTag -> * where
    PatConsF -- Constructor pattern match, e.g. (Just a : xs)
        :: grow (PattT PatConsT)
        -> String -- Constructor name
        -> [rec PattTree] -- Argument patterns
        -> PattF grow rec PattTree
    BareF -- Bare variable to bind to, e.g. x
        :: grow (PattT BareT)
        -> String -- Variable Name
        -> PattF grow rec PattTree

deriving instance (forall (a :: ConsTag). Show (grow a), forall (b :: TreeTag). Show (rec b))
  => Show (PattF grow rec tag)

-- The base higher-order functor for names, NameF
data NameF :: (ConsTag -> *) -> (TreeTag -> *) -> TreeTag -> * where
    AnyNameF -- Constructor for any possible name
        :: grow (NameT AnyNameT)
        -> String
        -> NameVariety
        -> NameLevel
        -> NameF grow rec NameTree

deriving instance (forall (a :: ConsTag). Show (grow a), forall (b :: TreeTag). Show (rec b))
  => Show (NameF grow rec tag)

data NameVariety
    = Regular -- E.g. f, Just, Maybe
    | Special -- E.g. +, <$>, :+:
    deriving (Show)

data NameLevel
    = Variables -- e.g. f, x, <$>
    | ConsAndTypes -- e.g. Just, Nothing, :+:
    deriving (Show)

-- ==================== COMPILER PASSES & ANNOTATIONS =========================

-- Annotation / compiler passes
data Pass a = Parsing | TypeInference | Custom a

-- Applied from Parsing stage:
data Offset = Offset Int | Phantom

-- Applied from TypeInference stage:
data Type

-- Annotation families, ala "Trees That Grow"
type family Annotation (pass :: Pass a) (t :: ConsTag) :: * where
    Annotation Parsing       t = Offset
    Annotation TypeInference t = Type
    Annotation (Custom a)    t = a

type family Annotations (passes :: [Pass a]) (tag :: ConsTag) where
    Annotations '[]       t = '[]
    Annotations (x ': xs) t = (Annotation x t ': Annotations xs t)

-- Lift the annotation
newtype Ann passes tag = Ann 
    { ann :: HList (Annotations passes tag) }

pattern ANil = Ann HNil

deriving instance (Show (HList (Annotations passes tag))) => Show ((Ann passes tag))

-- -- TESTING
-- newtype Recursor e = Recursor { derec :: [String] }
--     deriving (Show)
-- 
-- rebind :: Recursor a -> Recursor b
-- rebind = Recursor . derec
-- 
-- instance Semigroup (Recursor e) where
--     (derec -> a) <> (derec -> b) = Recursor $ a ++ b
-- instance Monoid (Recursor e) where
--     mempty = Recursor []
-- 
-- allExprNames :: ExprF passes Recursor tag -> Recursor tag
-- allExprNames = \case
--    VarF name -> Recursor [name]
--    IfF (rebind -> bool) (rebind -> true) (rebind -> false) -> bool <> true <> false
--    AppF _ (rebind -> func) (rebind -> arg) -> func <> arg
--    LitNumF _ -> Recursor []
--    AnyExprF (rebind -> e) -> e
-- 
-- allNames :: Annotated passes TreeF Recursor tag -> Recursor tag
-- allNames = algAnn $ algSum allExprNames (const $ Recursor [])
-- 
-- --ex1, ex2 :: HFix (ExprF passes) ('ExprT 'IfT)
-- --ex1
-- --  = HIn (IfF
-- --        (HIn $ AnyExprF $ HIn $ VarF "hello")
-- --        (HIn $ AnyExprF $ HIn $ VarF "hello")
-- --        (HIn $ AnyExprF $ HIn $ VarF "hello"))
-- --ex2
-- --  = HIn (IfF
-- --        (HIn $ AnyExprF $ HIn (AppF Prefix
-- --            (HIn $ AnyExprF $ HIn $ VarF "positive")
-- --            (HIn $ AnyExprF $ HIn $ VarF "x")))
-- --        (HIn $ AnyExprF $ HIn $ AnyExprF $ HIn $ VarF "posVal")
-- --        (HIn $ AnyExprF $ HIn $ AnyExprF $ HIn $ VarF "negVal"))

data Dummy a = Dummy
    deriving (Show)

ex3 :: HFix (TreeF (Ann '[])) ExprTree
ex3
  = If ANil
        (App ANil Prefix
            (App ANil Prefix
                (Var ANil ">")
                (Var ANil "a"))
            (Var ANil "b"))
        (App ANil Prefix
            (App ANil Prefix
                (Var ANil "-")
                (Var ANil "a"))
            (Var ANil "b"))
        (App ANil Prefix
            (App ANil Prefix
                (Var ANil "-")
                (Var ANil "b"))
            (Var ANil "a"))
