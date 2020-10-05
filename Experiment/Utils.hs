{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Bubble.Utils where

-- MISC
type GrowHoF grow k = HoF grow -> HoF k -> HoF k

-- ======================== TYPE-LEVEL LISTS ==================================
-- Take Type-Level Lists to Value-Level Tuples
data HList :: [*] -> * where
    HNil :: HList '[]
    (:>) :: x -> HList xs -> HList (x ': xs)

pattern HEnd x = x :> HNil
pattern x ::> y = x :> HEnd y

infixr :>
infixr ::>

instance Show (HList '[]) where
    show _ = "HNil"

instance (Show (HList xs), Show x) => Show (HList (x ': xs)) where
    show (x :> xs) = show x ++ " :> " ++ show xs

-- ======================== HIGHER ORDER FUNCTORS =============================
-- Kind-level helper synonyms for Higher-order Functors
type HoF k = k -> *
type BaseHoF k = HoF k -> HoF k

-- Create HFunctor instance for higher-order functors
class HFunctor f where
    hmap :: (forall anytag. r anytag -> r' anytag)
         -> f r tag -> f r' tag

-- Fix a base higher-order functor into its recursive tree
data HFix (hf :: BaseHoF k) (a :: k)
    = HIn { hout :: hf (HFix hf) a }

deriving instance (forall g. Show (g b) => Show (hf g b)) => Show (HFix hf b)

-- ======================== DATA TYPES A LA CARTE =============================
-- Summing over higher-order functors
data Sum (f :: GrowHoF p k) (g :: GrowHoF p k) (passes :: HoF p) (rec :: HoF k) (a :: k)
    = InL (f passes rec a)
    | InR (g passes rec a)

-- The void higher-order functor, for tying off sums
data VoidHoF :: GrowHoF passes k

-- Fold Sum over a type-level list
type family Sums (functors :: [GrowHoF p k]) :: GrowHoF p k where
    Sums '[] = VoidHoF
    Sums (f ': gs) = Sum f (Sums gs)

instance
    ( Show (f grow rec tag)
    , Show (g grow rec tag)
    ) => Show (Sum f g grow rec tag) where
    show x
      = label ++ " " ++ sub
        where
            label = case x of
                        InL _ -> "InL"
                        InR _ -> "InR"
            sub = case x of
                    InL f -> show f
                    InR g -> show g

instance Show (VoidHoF passes rec tag) where
    show _ = "VoidHoF"

-- ======================== RECURSION SCHEMES =================================
-- F-algebra over higher-order functors
type HoAlg (f :: BaseHoF k) (rec :: HoF k)
  = forall (tag :: k). f rec tag -> rec tag

-- Recursion schemes over higher-order functors
cata :: forall f tag rec
     . (HFunctor f)
     => HoAlg f rec -> HFix f tag -> rec tag
cata algebra (HIn x) =
    algebra (hmap (cata algebra) x)

-- Recursion scheme combinator for sums
algSum :: (f passes rec tag -> rec tag)
       -> (g passes rec tag -> rec tag)
       -> Sum f g passes rec tag -> rec tag
algSum algebra _ (InL left) = algebra left
algSum _ algebra (InR right) = algebra right

