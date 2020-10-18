module Main (main) where

import Bubble.Examples
import Bubble.IO
import Bubble.Expr
import Bubble.Parser
import Bubble.Lift
import Bubble.Optimizations

main = do
    let ls = do
            line <- getLine
            if null line
               then pure []
               else (line :) <$> ls
    clearLine
    putStrLn "Please enter your expression."
    str <- unlines <$> ls
    repl' $ refine (parse str) primitives

