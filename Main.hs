{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Bubble.Examples
import Bubble.IO
import Bubble.Expr
import Bubble.Parser
import Bubble.Lift
import Bubble.Breadcrumbs
import Bubble.Optimizations

import Network.Wai
import Network.HTTP.Types.Status
import Network.HTTP.Types.Header
import Network.Wai.Handler.Warp

import qualified Data.ByteString.Lazy.Char8 as DBC
import qualified Data.ByteString.Char8 as BC

import Data.IORef

main :: IO ()
main = server ex_simple'

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
    pure ()

accessAnything = [("Access-Control-Allow-Origin", "*"), ("Access-Control-Allow-Headers", "*")]

server :: Expr Redex -> IO ()
server initial = do
    liveExpr <- newIORef initial
    run 9001 $ \req handler -> do
        let path = pathInfo req
        let returnExpr = do
                text <- exprToJsonString <$> readIORef liveExpr
                handler $ responseLBS ok200 accessAnything (DBC.pack text)
        case path of
              ("get":_) -> do
                  print "Getting expression, w/o changes"
                  returnExpr
              ("reset":_) -> do
                  print "Resetting expression."
                  writeIORef liveExpr initial
                  returnExpr
              ("trail":_) -> do
                  print "Crumbtrail received."
                  body <- DBC.unpack <$> strictRequestBody req
                  case jsonStringToCrumbtrail body of
                      Nothing -> do
                          putStrLn "No crumbtrail parsed, returning same expression."
                      Just crumb -> do
                          putStrLn "Crumbtrail parsed:"
                          print body
                          modifyIORef liveExpr (\expr -> rerefine $ autorun $ rerefine $ autorun $ eat (sprinkle expr) crumb)
                  returnExpr
              _ -> do
                  print "Couldn't get useful path, retrieving file."
                  let filepath = "./ui" ++ if null path then "/index.html" else BC.unpack (rawPathInfo req)
                  print filepath
                  handler $ responseFile ok200 accessAnything filepath Nothing

