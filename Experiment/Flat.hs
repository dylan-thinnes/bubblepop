{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Experiment.Flat where

data TreeTag = TypeTree | ExprTree | DeclTree
data ConsTag = ExprT ExprTag | TypeT TypeTag
data ExprTag = VarT | IfT | AppT | LitNumT | AnyExprT
data TypeTag = ForallT | TyAppT | ConcreteT | BoundT
data DeclTag = AssignT | ImportT | ModuleT

type family Constructors (cons :: ConsTag) (rec :: HoF TreeTag) where
    Constructors (ExprT LitNumT) rec = Int
    Constructors (ExprT IfT)     rec = (rec ExprTree, rec ExprTree, rec ExprTree)
    Constructors (TypeT BoundT)  rec = String
    Constructors (TypeT TyAppT)  rec = (rec TypeTree, rec TypeTree)
    Constructors (TypeT ForallT) rec = [rec TypeTree]

type HoF k = k -> *
type BaseHoF k = HoF k -> HoF k

data Quant (meta :: ConsTag -> HoF TreeTag -> *) (rec :: HoF TreeTag) (tree :: TreeTag)
    = Quant (forall (cons :: ConsTag). meta cons rec)

data Dummy (x :: TreeTag) = Dummy

data HFix (hf :: BaseHoF k) (a :: k)
    = HIn { hout :: hf (HFix hf) a }
