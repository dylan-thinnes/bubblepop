{-# LANGUAGE LambdaCase, MultiWayIf #-}
module Bubble.IO where

import Bubble.Expr
import Data.Functor.Foldable hiding (Cons)
import qualified Data.List.NonEmpty as N
import Data.List.NonEmpty (NonEmpty(..), (<|))

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
        toLines (AppF body args) = body <> indent (nec args)
        toLines (AbsF args body) = parenthesize $ ("\\" ++ unwords args ++ " ->") <| indent body
        toLines (VarF name) = line name
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

pretty :: Either String Expr -> IO ()
pretty = \case
    Left e -> putStrLn $ "Error: " ++ e
    Right e -> putStrLn $ prettyRaw $ ruin e

repl :: String -> Expr -> IO Expr
repl str expr = do
    putStr "\ESC[2J\ESC[H"
    putStrLn "============================================"
    putStrLn str
    putStrLn $ prettyRaw $ ruin expr
    let options = crumbtrails expr
    if null options then pure expr
        else do
            mapM_ (uncurry showOption) (zip [0..] options)
            i <- readLn
            if | i < 0 -> pure expr
               | i >= length options -> repl "Error: Option index out of bounds." expr
               | otherwise -> do
                    let crumb = options !! i
                    case hansel expr crumb of
                      Left err -> repl ("Error: " ++ err) expr
                      Right newExpr -> repl "Success." $ rerefine newExpr
    where
        showOption i option = putStr (show i ++ ": ") >> print option


