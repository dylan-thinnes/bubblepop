module Bubble.Optimizations where

import Bubble.Expr
import Bubble.Breadcrumbs

import Data.Sequence (Seq)
import Control.Comonad.Cofree
import Data.Bifunctor
import Data.Functor.Foldable

type Original = ListMapRose Crumbtrail (Expr Redex)
type Collapsed = ListMapRose (Seq Crumbtrail) (Expr Redex)

data NonEmpty f a = NonEmpty a (f a)

collapse :: Original -> Collapsed
collapse = cata (\(expr :<: branches) -> expr :< (ListMap $ map (first pure) $ unLMap branches))

--autorun :: Original -> Original
--autorun = cata (\(expr :<: branches) -> expr :< (f =<< branches))
--    where
--        f (AnnCont "autorun" : rest, _) = undefined
--
--lasts :: ListMapRose a b -> [b]
--lasts = cata (\(expr :<: branches) -> if null branches then [expr] else concat branches)
