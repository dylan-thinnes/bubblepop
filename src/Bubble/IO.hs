{-# LANGUAGE LambdaCase, MultiWayIf, ViewPatterns, TypeApplications #-}
module Bubble.IO where

import Bubble.Expr
import Bubble.Breadcrumbs
import Data.Functor.Foldable hiding (Cons)
import qualified Data.List.NonEmpty as N
import Data.List.NonEmpty (NonEmpty(..), (<|))
import Prettyprinter
import Prettyprinter.Render.Util.SimpleDocTree
import qualified Data.Text as T
import Text.JSON
import Data.Functor.Product (Product(..))

import Control.Monad.State
import Data.Maybe (isJust)
import Control.Comonad.Cofree
import Data.Functor.Const

{------------------------------------------------------------------------------
                             IO & USER INTERACTION
------------------------------------------------------------------------------}

prettyRaw :: RawExpr -> String
prettyRaw = unlines . N.toList . cata toLines
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
        parenthesize x = ("(" :| []) `fuse` x `fuse` (")" :| [])

        fuse :: NonEmpty String -> NonEmpty String -> NonEmpty String
        fuse (a :| []) (b :| bs) = (a ++ b) :| bs
        fuse (a :| as) (b :| bs) = a :| (init as ++ [last as ++ b] ++ bs)

        toLines :: RawExprF (NonEmpty String) -> NonEmpty String
        toLines (LitF lit) = line $ prettyLit lit
        toLines (AnnF _ cont) = cont
        toLines (AppF body args) = body <> indent (nec args)
        toLines (AbsF args body) = parenthesize $ ("\\" ++ unwords args ++ " ->") <| indent body
        toLines (VarF name) = line $ string name -- TODO: infix operators need parens
        toLines (IfF cond true false) = line "if" <> indent cond <> line "then" <> indent true <> line "else" <> indent false
        toLines (PrimOpF op) = line $ show op
        toLines (LetF name bound body) = line ("let " ++ prettyName name Prefix ++ " =") <> indent bound <> line "in" <> indent body
        toLines (EConsF (Cons name args)) =
            case fixity name of -- Very messy...
              Prefix -> nec' (prettyName name Prefix) (indent <$> args)
              Infix  -> case args of
                          (x:y:xs) ->
                              if length x <= 1
                                  then x `fuse` line (prettyName name Infix) `fuse` nec (y:xs)
                                  else x <> indent (nec' (prettyName name Infix) xs)
                          (x:[]) ->
                              if length x <= 1
                                  then parenthesize $ x `fuse` line (prettyName name Infix)
                                  else x <> indent (line (prettyName name Infix))
                          ([]) -> line (prettyName name Prefix)
        toLines (CaseF scrutee branches) = parenthesize $ line "case" <> indent scrutee <> nec' "of" (indent . handleBranch <$> branches)
            where
                handleBranch (pat, body) = line (prettyPat pat ++ " ->") <> indent body

--pretty :: Either String Expr -> IO ()
--pretty = \case
--    Left e -> putStrLn $ "Error: " ++ e
--    Right e -> putStrLn $ prettyRaw $ ruin e

repl :: String -> Expr Redex -> IO (Expr Redex)
repl str expr = do
    clearLine
    putStrLn str
    putStrLn $ prettyRaw $ ruin expr
    let sprinkled = sprinkle expr
    let options = pickup sprinkled
    if null options then pure expr
        else do
            mapM_ (uncurry showOption) (zip [0..] options)
            i <- readLn
            if | i < 0 -> pure expr
               | i >= length options -> repl "Error: Option index out of bounds." expr
               | otherwise -> do
                    let crumb = options !! i
                    repl "Success." $ rerefine $ autorun $ rerefine $ autorun $ eat sprinkled crumb
    where
        showOption i option = putStr (show i ++ ": ") >> print option

repl' :: Expr Redex -> IO (Expr Redex)
repl' orig = recurse "Started..." $ stepAll orig
    where
        showOption i (trail, _) = putStr (show i ++ ": ") >> print trail
        recurse message self@(expr :< (unLMap -> branches)) = do
            clearLine
            putStrLn message
            putStrLn $ prettyRaw $ ruin expr
            if null branches
               then pure expr
               else do
                    mapM_ (uncurry showOption) (zip [0..] branches)
                    i <- readLn
                    if | i < 0
                       -> do
                           putStrLn "Aborting early due to negative index."
                           pure expr
                       | i >= length branches
                       -> recurse "Error: Option index out of bounds." self
                       | otherwise
                       -> recurse "Success" $ snd $ branches !! i

clearLine :: IO ()
clearLine = do
    putStr "\ESC[2J\ESC[H"
    putStrLn "============================================"

docRaw' :: Expr (Const (Redex (Crumbtrail, a))) -> Doc Crumbtrail
docRaw' = cata h
    where
        h :: ExprF (Const (Redex (Crumbtrail, a))) (Doc Crumbtrail) -> Doc Crumbtrail
        h (Pair expr (Const NoRedex)) = f expr
        h (Pair expr (Const (Redex (crumb, _)))) = annotate crumb $ f expr

        f :: RawExprF (Doc Crumbtrail) -> Doc Crumbtrail
        f (LitF lit) = pretty $ prettyLit lit
        f (AnnF _ cont) = cont
        f (AppF body args) = hang 4 $ body <+> align (sep args) -- TODO: Infix operators, precedence for paren-wrapping
        f (AbsF args body) = hang 4 $ (pretty "\\" <> fillSep (map pretty args ++ [pretty "->"])) <+> body
        f (VarF name) = pretty (string name) -- TODO: Infix operators in prefix context
        f (IfF cond true false) = pretty "if" <+> nest 4 cond <+> pretty "then" <+> nest 4 true <+> pretty "else" <+> nest 4 false
        f (PrimOpF op) = pretty $ show op
        f (LetF name bound body) = vsep [pretty "let" <+> pretty (string name) <+> pretty "=" <+> nest 4 bound, pretty "in" <+> body]
        f (EConsF (Cons name args)) = pretty (string name) <+> nest 4 (sep args)
        f (CaseF scrutee branches) = vsep (pretty "case" <+> nest 4 scrutee <+> pretty "of" : map handle branches)
            where
                handle (pat, branch) = hang 4 $ pretty (prettyPat pat) <+> pretty "->" <+> branch

data UIAST = Nodes [UIAST] | Crumbed Crumbtrail UIAST | Raw T.Text

renderUIAST :: SimpleDocTree Crumbtrail -> UIAST
renderUIAST sds = case sds of
    STEmpty -> Raw mempty
    STChar c -> Raw $ T.singleton c
    STText _ t -> Raw t
    STLine i -> Raw $ T.pack $ "\n" <> replicate i ' '
    STAnn ann content -> Crumbed ann (renderUIAST content)
    STConcat contents -> Nodes $ renderUIAST <$> contents

instance JSON UIAST where
    readJSON = error "Cannot turn JSON into a UIAST - unimplemented!"
    showJSON (Nodes nodes) = showJSON (fmap showJSON nodes)
    showJSON (Crumbed trail node) = showJSON $ toJSObject [("crumbtrail", showJSON trail), ("child", showJSON node)]
    showJSON (Raw text) = showJSON text

instance JSON Crumb where
    readJSON = fmap read <$> (readJSON @String)
    showJSON = showJSON . show

exprToJsonString :: Expr Redex -> String
exprToJsonString = encode . renderUIAST . treeForm . layoutPretty defaultLayoutOptions . docRaw' . sprinkle
