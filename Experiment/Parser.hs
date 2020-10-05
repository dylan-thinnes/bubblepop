{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExistentialQuantification #-}
module Bubble.Parser where

import Text.Megaparsec hiding (getOffset)
import qualified Text.Megaparsec as M
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Text (Text)

import Data.Void

import Bubble.Data

-- type Parser = Parsec Void Text
-- 
-- data Q f = forall (a :: ExprTag). Q { unquant :: f (ExprT a) }
-- 
-- getOffset :: Parser (HList '[Offset])
-- getOffset = HEnd . Offset <$> M.getOffset
-- 
-- type ExprWrap expr = Everything '[Parsing] TreeF (ExprT expr)
-- 
-- parseNotApp :: Parser (ExprWrap AnyExprT)
-- parseNotApp = try (AnyExpr (HEnd Phantom) <$> parseLitNum)
--           <|> try (AnyExpr (HEnd Phantom) <$> parseIf)
--           <|> try (AnyExpr (HEnd Phantom) <$> parseVar)
-- 
-- parseExpr :: Parser (ExprWrap AnyExprT)
-- parseExpr = try (AnyExpr (HEnd Phantom) <$> parseNotApp)
--         <|> try (AnyExpr (HEnd Phantom) <$> parseApp)
-- 
-- parseLitNum :: Parser (ExprWrap LitNumT)
-- parseLitNum = LitNum <$> getOffset <*> L.decimal
-- 
-- parseVar :: Parser (ExprWrap VarT)
-- parseVar = do
--     x <- letterChar
--     xs <- some alphaNumChar
--     let name = x : xs
--     off <- getOffset
--     pure $ Var off name
-- 
-- parseIf :: Parser (ExprWrap IfT)
-- parseIf = do
--     string "if"
--     space1
--     bool <- parseExpr
--     string "then"
--     space1
--     true <- parseExpr
--     string "else"
--     space1
--     false <- parseExpr
--     off <- getOffset
--     pure $ If off bool true false
-- 
-- parseApp :: Parser (ExprWrap AppT)
-- parseApp = do
--     fun <- parseExpr
--     space1
--     var <- parseNotApp
--     off <- getOffset
--     pure $ App off Prefix fun var
