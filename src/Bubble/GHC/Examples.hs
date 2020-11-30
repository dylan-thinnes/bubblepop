{-# LANGUAGE TemplateHaskell, RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PackageImports  #-}
module Bubble.GHC.Examples where

import Bubble.GHC.Expr
import Bubble.GHC.Classes
import "template-haskell" Language.Haskell.TH hiding (ppr, pprint)
import "template-haskell" Language.Haskell.TH.Syntax
import Text.PrettyPrint.Annotated (Span(..))
import Bubble.GHC.Ppr (ppr, pprint, pprintWithSpans)
import Bubble.GHC.PprLib (Ann)
import Data.Monoid (Last(..), First(..))
import Data.List (intersperse, groupBy, foldl')
import Data.Function (on)

plus =
    let primOpName = Name (OccName "+") NameS
        primOpContract = [Integer, Integer]
        primOpFunc = \[IntegerL i, IntegerL j] -> IntegerL $ i + j
    in
    (primOpName, FP (-1) NoRedex $ PrimOp {..})

times =
    let primOpName = Name (OccName "*") NameS
        primOpContract = [Integer, Integer]
        primOpFunc = \[IntegerL i, IntegerL j] -> IntegerL $ i * j
    in
    (primOpName, FP (-1) NoRedex $ PrimOp {..})

liftCommendDefinePrims raw = hatchAll $ foldr replace (commend raw) [plus, times]

ex1 = liftCommendDefinePrims $(liftEx [| 2 * (1 + 3 * 5) |])
ex2 = liftCommendDefinePrims $(liftEx [| 2 * (1 + (3) * 5) |])
ex3 = liftCommendDefinePrims $(liftEx [| (2 * 2) + (3 * 5) |])
ex4 = liftCommendDefinePrims $(liftEx [|
    (\a b c d -> if a then 2 * b else b + c * d)
        False
        4
        5
        6
    |])
ex5 = liftCommendDefinePrims $(liftEx [| (\(Just x) -> x) (Just 5) |])
ex6 = liftCommendDefinePrims $(liftEx [|
    case Just (Just 4) of
      Just (Just 3) -> 5
      Just (Just x) -> x
      Just Nothing -> 1
      Nothing -> 0
    |])
ex7 = liftCommendDefinePrims $(liftEx [|
    case "abc" of
      x:y:_ -> x:y:[]
      x:xs -> x:[]
      _ -> 'c'
    |])
ex8 = liftCommendDefinePrims $(liftEx [|
    case ['a','b','c'] of
      x:y:_ -> x:y:[]
      x:xs -> x:[]
      _ -> 'c'
    |])

insertListAt :: Int -> [a] -> [a] -> [a]
insertListAt i insertion list = let (head, tail) = splitAt i list in head ++ insertion ++ tail

colorFrom :: Int -> String
colorFrom i = "\ESC[1;3" ++ show (1 + i `mod` 6) ++ "m"
resetColor, bold :: String
resetColor = "\ESC[0m"
bold = "\ESC[1m"

type Paved = [(Last Int, Char)]

prepave :: String -> Paved
prepave = map (mempty,)

paveSpan :: (Int, Span Ann) -> Paved -> Paved
paveSpan (i, Span {..}) paved = zipWith (\(a,b) c -> (a <> c, b)) paved (leftPad ++ coloration ++ repeat mempty)
    where
        leftPad = replicate spanStart mempty
        coloration = replicate spanLength (pure spanAnnotation)

depave :: Paved -> String
depave paved = concatMap colorize groups
    where
        groups = map sequence $ groupBy ((==) `on` fst) paved
        colorize (Last mi, text) =
            case mi of
              Nothing -> bold <> text <> resetColor
              Just i -> colorFrom i <> text <> resetColor

pave :: [Span Ann] -> String -> Paved
pave spans text = foldl' (flip paveSpan) (prepave text) (zip [0..] spans)

--paveExpG :: ExpG Redex -> [(Last Int, String)]
paveExpG expg = paved
    where
        (text, spans) = pprintWithSpans expg
        paved = pave spans text
        groups = map sequence $ groupBy ((==) `on` fst) paved

repl :: ([Int] -> IO String) -> ExpG Redex -> IO ()
repl input expr = do
    let (text, spans) = pprintWithSpans expr
    putStrLn $ depave $ pave spans text
    let ids = map spanAnnotation spans
    case ids of
        [] -> pure ()
        ids@(defaultId:_) -> do
            idRaw <- input ids
            case reads idRaw of
                []         -> repl input $ hatchAll $ eat defaultId expr
                (id, ""):_ -> repl input $ hatchAll $ eat id expr
                _          -> repl input expr

replAuto, replGuided :: ExpG Redex -> IO ()
replAuto = repl $ \_ -> do
    putStrLn "==="
    pure ""
replGuided = repl $ \ids -> do
    let coloredIds = zipWith (\index id -> colorFrom id ++ show id ++ resetColor) [0..] ids
    putStrLn $ concat $ intersperse ", " coloredIds
    getLine
