{-# LANGUAGE OverloadedStrings #-}

module Parser where

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

braces, parens, chevrons :: Parser a -> Parser a
parens = between (char '(') (char ')')
braces = between (lexeme $ char '{') (lexeme $ char '}')
chevrons = between (char '<') (char '>')

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

-- Pack{num, num}
prsPack :: Parser CoreExpr
prsPack = braces $ do
  tag <- integer
  symbol ","
  arity <- integer
  return $ EConstr tag arity

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
  symbol "case"
  expr <- prsExpr
  symbol "of"
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
  defns <- prsDefns
  symbol "in"
  expr <- prsExpr
  return $ ELet nonRecursive defns expr

prsLetrec = do
  symbol "letrec"
  defns <- prsDefns
  symbol "in"
  expr <- prsExpr
  return $ ELet recursive defns expr

prsApp = do
 to_apply <- prsExpr
 arg <- prsAExpr
 return $ EAp to_apply arg

-- this is a seperate function for testing purposes
prsParensExpr = parens prsExpr

prsAExpr = prsVar <|> prsNum <|> prsPack <|> prsParensExpr
-- do not parse lambdas until I get to lambda lifting for convenience
prsExpr = prsLet <|> prsLetrec <|> prsCase <|> prsApp <|> prsAExpr -- temporary
