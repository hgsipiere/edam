{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Control.Applicative hiding (some, many)
import Data.Text (Text)
import Data.Void

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Type

type Parser = Parsec Void Text

-- happy comments
spaceConsumer :: Parser ()
spaceConsumer = L.space space1
  (L.skipLineComment "#") (L.skipBlockComment "(:" ":)")

-- how to consume space after! given parser
lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

symbol = L.symbol spaceConsumer
integer = lexeme L.decimal
charLexeme = lexeme.char

braces, parens, chevrons :: Parser a -> Parser a
parens = between (charLexeme '(') (charLexeme ')')
braces = between (charLexeme '{') (charLexeme '}')
chevrons = between (charLexeme '<') (charLexeme '>')
moduli = between (charLexeme '|') (charLexeme '|')

-- var -> alpha varch_1 ... varch_n n >= 0, varch -> alpha | digit | _
prsIdent :: Parser Name
prsIdent = lexeme $ do
  initial <- lowerChar
  rest <- many (alphaNumChar <|> char '_')
  return (initial:rest)

prsNum :: Parser CoreExpr
prsNum = ENum <$> integer

prsVar :: Parser CoreExpr
prsVar = EVar <$> prsIdent

prsPack :: Parser CoreExpr
prsPack = symbol "Pack" *> (braces $ do
  tag <- integer
  symbol ","
  arity <- integer
  return $ EConstr tag arity)

prsAlt :: Parser CoreAlt
prsAlt = do
  tag <- chevrons integer
  vars <- many prsIdent
  symbol "->"
  expr <- prsExpr
  return $ corealt tag vars expr

prsAlts :: Parser [CoreAlt]
prsAlts = do
  x <- prsAlt
  xs <- many prsAlt
  return $ x:xs

prsCase :: Parser CoreExpr
prsCase = do
  expr <- moduli prsExpr
  alts <- prsAlts
  return (ECase expr alts)

prsDefn :: Parser CoreDefn
prsDefn = do
  ident <- prsIdent
  symbol "="
  meaning <- prsExpr
  return $ coredefn ident meaning

prsDefns :: Parser [CoreDefn]
prsDefns = do
  defn <- prsDefn
  defns <- many $ symbol ";" *> prsDefn
  return $ defn:defns

prsLet = do
  symbol "let"
  defns <- chevrons prsDefns
  expr <- prsExpr
  return $ ELet nonRecursive defns expr

prsLetrec = do
  symbol "letrec"
  defns <- chevrons prsDefns
  expr <- prsExpr
  return $ ELet recursive defns expr

-- this is like this rather than expr aexpr
-- because then the grammar becomes left recursive
prsApp = mkApChain <$> some prsAExpr

-- this is a seperate function for testing purposes
prsParensExpr = parens prsExpr

prsAExpr = prsVar <|> prsNum <|> prsPack <|> prsParensExpr
-- do not parse lambdas until I get to lambda lifting for convenience
prsExpr = prsLet <|> prsLetrec <|> prsCase <|> prsApp <|> prsAExpr
