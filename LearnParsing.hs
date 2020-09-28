{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
module LearnParsing where

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void

type Parser = Parsec Void Text

data URI = URI
    { scheme :: Scheme
    , authority :: Maybe Authority
    }
    deriving (Eq, Show)

data Scheme = Data | File | FTP | HTTP | HTTPS | IRC | Mailto
    deriving (Eq, Show)

data Authority = Authority
    { credentials :: Maybe Credentials
    , host :: Text
    , port :: Maybe Int
    }
    deriving (Eq, Show)

data Credentials = Credentials
    { user :: Text
    , password :: Text
    }
    deriving (Eq, Show)

pScheme :: Parser Scheme
pScheme
  = choice
    [ Data   <$ string "data"
    , File   <$ string "file"
    , FTP    <$ string "ftp"
    , HTTP   <$ string "http"
    , HTTPS  <$ string "https"
    , IRC    <$ string "irc"
    , Mailto <$ string "mailto"
    ]

pHost :: Parser Text
pHost = T.pack <$> some (alphaNumChar <|> char '.')

pAuthority :: Parser Authority
pAuthority = do
    credentials <- optional $ try $ do
        user <- T.pack <$> some alphaNumChar
        char ':'
        password <- T.pack <$> some alphaNumChar
        char '@'
        pure $ Credentials {..}
    host <- pHost
    port <- optional $ try $ char ':' >> L.decimal
    pure $ Authority {..}

pURI :: Parser URI
pURI = do
    scheme <- pScheme <?> "valid scheme"
    single ':'
    authority <- optional $ do
        string "//"
        pAuthority
    pure $ URI {..}

eofify :: Parser a -> Parser a
eofify p = p <* eof
