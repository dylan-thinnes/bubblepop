module Bubble.Parser where

import Prelude hiding (abs)

import Bubble.Expr hiding (string)
import Text.ParserCombinators.ReadP
import Control.Monad
import Data.Char (isSpace, isLower, isUpper, isAlpha, isDigit)
import GHC.Exts (fromString)

-- Names
--data Name = Name
--    { string :: String
--    , fixity :: Fixity
--    , variety :: Variety
--    }
--    deriving (Show, Eq)
--data Fixity = Infix | Prefix
--    deriving (Show, Eq)
--data Variety = Con | Var
--    deriving (Show, Eq)

lower, upper, alpha, digit, symbol :: ReadP Char
lower = satisfy isLower
upper = satisfy isUpper
alpha = satisfy isAlpha
digit = satisfy isDigit
symbol = satisfy (`elem` "!#$%&⋆+./<=>?@\\^|-~:")

simpleName :: ReadP String -- TODO: remove when AbsF takes patterns
simpleName = do
    name <- (++) <$> munch1 isAlpha <*> munch (== '\'')
    guard $ not $ name `elem` ["if","then","else","case","of","let","in"]
    pure name

name :: ReadP Name
name = do
    str <- choice [prefix, infix_]
    -- guard against reserved keywords
    guard $ not $ str `elem` ["\\","..","::","|","<-","->","@","~","=>"]
    pure $ fromString str
    where
        prefix = simpleName
        infix_ = munch1 (`elem` "!#$%&*+./<=>?@\\^|-~:")

white, white1 :: ReadP ()
white = munch isSpace >> pure ()
white1 = munch1 isSpace >> pure ()
space = munch (== ' ') >> pure ()
space1 = munch1 (== ' ') >> pure ()

var :: ReadP RawExpr
var = VarR <$> name

literal :: ReadP Literal
literal = choice [Int <$> int, Char <$> character, String <$> string]
    where
    int = do
        minus <- option Nothing (Just <$> char '-')
        num <- read <$> munch1 isDigit
        pure $ if minus == Nothing then num else negate num
    escapable end = do
        pre <- satisfy (const True)
        if pre /= '\\'
           then pure pre
           else do
               c <- satisfy (const True)
               case lookup c [(end, end), ('n', '\n'), ('\\', '\\')] of -- TODO: add more special char cases
                 Nothing -> pure c
                 Just c -> pure c
    character = between (char '\'') (char '\'') (escapable '\'')
    string = do
        char '"'
        manyTill (escapable '"') (char '"')

eliteral :: ReadP RawExpr
eliteral = LitR <$> literal

app :: ReadP RawExpr
app = do
    (func:args) <- sepBy1 (choice [between (char '(') (char ')') expr, var, eliteral]) space1
    pure $ AppR func args

abs :: ReadP RawExpr
abs = do
    char '\\'
    args <- sepBy1 simpleName white1
    white
    string "->"
    white
    body <- expr
    pure $ AbsR args body

if_ :: ReadP RawExpr
if_ = do
    string "if"
    white1
    cond <- expr
    white1
    string "then"
    white1
    true <- expr
    white1
    string "else"
    white1
    false <- expr
    pure $ IfR cond true false

cons :: ReadP a -> ReadP (Cons a)
cons sub = do
    n <- name
    guard $ variety n == Con
    white1
    args <- sepBy1 sub white1
    pure $ Cons n args

econs :: ReadP RawExpr
econs = do
    (Cons name args) <- cons $ choice [between (char '(') (char ')') expr, var, eliteral]
    pure $ EConsR name args

pattern_ :: ReadP (Pattern Name)
pattern_ = do
    choice [PCons <$> cons pattern_, char '_' >> pure PWildcard, PLiteral <$> literal, PEscape <$> name]

case_ :: ReadP RawExpr
case_ = do
    string "case"
    white1
    scrutee <- expr
    white1
    string "of"
    white1
    branches <- flip sepBy1 (space >> char '\n' >> space) $ do
        pat <- pattern_
        white
        string "->"
        white
        e <- expr
        pure (pat, e)
    pure $ CaseR scrutee branches

let_ :: ReadP RawExpr
let_ = do
    string "let"
    white1
    n <- name
    white
    string "="
    white
    e <- expr
    white1
    string "in"
    white1
    body <- expr
    pure $ LetR n e body

expr :: ReadP RawExpr
expr = choice [eliteral, var, app, abs, if_, econs, case_, let_]

parse :: String -> RawExpr
parse = fst . head . filter (null . snd) . readP_to_S p
    where
        p = do
            e <- expr
            white
            pure e
