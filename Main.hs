{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Bubble.Examples
import Bubble.IO
import Bubble.Expr
import Bubble.Parser
import Bubble.Lift
import Bubble.Optimizations

import Network.Wai
import Network.Wai.Handler.Warp

main = server

cli :: IO ()
cli = do
    let ls = do
            line <- getLine
            if null line
               then pure []
               else (line :) <$> ls
    clearLine
    putStrLn "Please enter your expression."
    str <- unlines <$> ls
    repl' $ refine (parse str) primitives

server :: IO ()
server = run 9001 $ \req handler -> do
	print "Request!"
	undefined
