{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Main where

import Data.String
import Text.ParserCombinators.ReadP
import Safe (headMay)
import Control.Monad

main :: IO ()
main = return ()

runReadP1 :: ReadP a -> String -> Maybe a
runReadP1 parser str
  = headMay $ do
      (parse, rest) <- readP_to_S parser str
      guard $ null rest
      pure parse

newtype Name = Name String
    deriving (Show, IsString)

data Source = Source Name [Decl]
    deriving (Show)
data Decl
    = Annot Name Type
    | Definition Name [Formal] Expr
    | Data Name [Name] [(Name, [Type])]
    | Synonym Name [Name] Type
    deriving (Show)
data Type
    = AppT Name Type
    | Concrete Name
    | Quantified Name
    deriving (Show)
data Formal
    = Head Name
    | ConstructorE Name [Formal]
    deriving (Show)
data Expr
    = Lambda [Formal] Expr
    | Variable Name
    | App Expr [Expr]
    | CharLiteral Char | IntegerLiteral Integer | StringLiteral String
    | List Expr
    -- | ListComp Expr [([Formal], Expr)]
    | Parens Expr
    deriving (Show)

whitespace :: ReadP ()
whitespace = munch (== ' ') >> pure ()

whitespace1 :: ReadP ()
whitespace1 = munch1 (== ' ') >> pure ()

parseName :: ReadP Name
parseName = Name <$> choice [prefix, infix_]
    where
    -- two kinds: prefix, infix
    -- two subkinds each: value-level, type-level
    prefix = do
        a <- satisfy prefixChar
        b <- munch (choiceP [num, prefixChar])
        c <- munch prime
        pure $ a : b ++ c
    infix_ = (:) <$> satisfy special <*> munch1 special
    -- utils
    choiceP xs c = or $ xs <*> [c]
    prefixChar = choiceP [uscore, lower, upper]
    uscore = (== '_')
    prime = (== '\'')
    lower = (`elem` ['a'..'z'])
    upper = (`elem` ['A'..'Z'])
    num = (`elem` ['0'..'9'])
    special = (`elem` "&|:<>=")

parseFormal :: ReadP Formal
parseFormal = Head <$> parseName

parseExpr :: ReadP Expr
parseExpr = choice [nonapp, app]
    where
        nonapp = choice [variable, charlit, intlit, strlit, lambda]
        variable = Variable <$> parseName
        charlit = do -- Currently, no escape sequences!
            char '\''
            c <- satisfy $ const True
            char '\''
            pure $ CharLiteral c
        intlit = do
            negative <- option False (char '-' >> pure True)
            digits <- many1 $ choice $ char <$> ['0'..'9']
            pure $ IntegerLiteral $ (if negative then negate else id) $ read digits
        strlit = do
            char '"'
            cs <- many $ satisfy $ (/= '"')
            char '"'
            pure $ StringLiteral cs
        lambda = do
            char '\\'
            formals <- sepBy1 parseFormal whitespace1
            whitespace
            string "->"
            whitespace
            body <- parseExpr
            pure $ Lambda formals body
        parens = Parens <$> between (whitespace >> char '(' >> whitespace) (whitespace >> char ')' >> whitespace) parseExpr
        app = do
            function <- nonapp
            arguments <- many $ char ' ' >> nonapp
            pure $ if null arguments then function else App function arguments

-- eval :: Expr -> Expr
