{-# LANGUAGE DeriveFunctor, DeriveFoldable, PatternSynonyms, TemplateHaskell #-}
module Bubble.Breadcrumbs where

import Bubble.Expr

import Data.Fix (Fix(..))
import Data.Functor.Foldable hiding (Cons)
import Data.Functor.Const
import Data.Functor.Product
import Data.Functor.Compose
import Control.Comonad.Cofree (Cofree(..))
import qualified Control.Comonad.Trans.Cofree
import Text.Show.Deriving (deriveShow1)

{------------------------------------------------------------------------------
                                  BREADCRUMBS
                         for indexing into expressions
------------------------------------------------------------------------------}

data Crumb
    = AppFunc | AppArg Int
    | AbsBody
    | IfCond | IfTrue | IfFalse
    | LetBound | LetBody
    | EConsArg Int
    | CaseBody | CaseBranch Int
    | AnnCont
    deriving (Show, Eq, Read)

type Crumbtrail = [Crumb]

attach :: Crumb -> Crumbtrail -> Crumbtrail
attach c trail = c : trail

-- Attach all crumbtrails to a expression tree
sprinkle :: Expr Redex -> Expr (Const (Redex (Crumbtrail, Expr Redex)))
sprinkle e = para f e []
    where
        f :: ExprF Redex (Expr Redex, Crumbtrail -> Expr (Const (Redex (Crumbtrail, Expr Redex))))
          -> Crumbtrail -> Expr (Const (Redex (Crumbtrail, Expr Redex)))
        f (Pair expr redex) trail = Fix $ Pair (children $ fmap attachTrail $ fmap snd expr) (Const (fmap (\hatch -> (trail, fst hatch)) redex))
            where
            attachTrail f crumb = f $ attach crumb trail

            children (LitF lit) = LitF lit
            children (PrimOpF op) = PrimOpF op
            children (VarF name) = VarF name
            children (AppF fun args) = AppF (fun AppFunc) (zipWith ($) args (map AppArg [0..]))
            children (AbsF names body) = AbsF names $ body AbsBody
            children (IfF cond true false) = IfF (cond IfCond) (true IfTrue) (false IfFalse)
            children (LetF name bound body) = LetF name (bound LetBound) (body LetBody)
            children (EConsF (Cons name args)) = EConsF (Cons name (zipWith ($) args (map EConsArg [0..])))
            children (CaseF body branches) = CaseF (body CaseBody) (zipWith (\(pat, branch) crumb -> (pat, branch crumb)) branches (map CaseBranch [0..]))
            children (AnnF ann cont) = AnnF ann $ cont AnnCont

-- Eat up the crumbs in a tree, quite inefficiently!
eatG :: (Crumbtrail -> Bool) -> (Expr Redex -> Expr Redex)
     -> Expr (Const (Redex (Crumbtrail, Expr Redex)))
     -> Expr Redex
eatG pred transform = cata f
    where
        f (Pair raw (Const (R Nothing))) = embed $ Pair raw NoRedex
        f (Pair raw (Const (R (Just (trail, oldRedex))))) =
            let oldExpr = embed $ Pair raw (Redex oldRedex)
             in if pred trail
                   then transform oldExpr
                   else oldExpr

eat :: Expr (Const (Redex (Crumbtrail, Expr Redex))) -> Crumbtrail -> Expr Redex
eat expr crumb = eatG (crumb ==) f expr
    where
        f (Fix (Pair _ (Redex redex))) = redex
        f redex = redex

-- Pickup / collect all the crumbs in a tree
pickup :: Expr (Const (Redex (Crumbtrail, a))) -> [Crumbtrail]
pickup = cata f
    where
        f (Pair raw (Const redex)) = mself ++ children
            where
            mself = case redex of
                      R Nothing -> []
                      R (Just (trail, _)) -> [trail]
            children = concat raw

-- Use the above to single-step out an indexed rose tree of all
-- breadcrumb-expr pairs
newtype ListMap k v = ListMap { unLMap :: [(k, v)] }
    deriving (Show, Functor, Foldable)
deriveShow1 ''ListMap

type ListMapRose k v = Cofree (ListMap k) v

step :: Expr Redex -> ListMap Crumbtrail (Expr Redex)
step expr =
    let sprinkled = sprinkle expr
        crumbtrails = pickup sprinkled
        remember f a = (a, f a)
     in ListMap $ map (remember $ rerefine . eat sprinkled) crumbtrails

stepAll :: Expr Redex -> ListMapRose Crumbtrail (Expr Redex)
stepAll = ana (\expr -> expr :<: step expr)

pattern a :<: b = a Control.Comonad.Trans.Cofree.:< b
