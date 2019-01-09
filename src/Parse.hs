{-# LANGUAGE FlexibleContexts #-}

module Parse (parse) where

import Control.Monad
import Data.Char (isMark, isPunctuation, isSymbol)
import Data.Functor
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Text.Parsec as Parsec
import Text.Parsec hiding (parse)

import Ast

type Parser = Parsec String ()

-- Use Parsec LanguageDef for easy handling of comments and reserved keywords
-- http://hackage.haskell.org/package/parsec-3.1.13.0/docs/Text-Parsec-Token.html

parse :: SourceName -> String -> Either ParseError Program
parse = Parsec.parse program

program :: Parser Program
program = do
  spaces
  defs <- fmap Map.fromList (sepEndBy def spaces)
  main <- maybe (fail "main function not defined") pure (Map.lookup (Id "main") defs)
  pure (Program main (Map.delete (Id "main") defs))

def :: Parser (Id, Expr)
def = parens (try (string "define" *> spaces1) *> (varDef <|> funDef))

varDef :: Parser (Id, Expr)
varDef = do
  name <- ident
  spaces1
  body <- expr
  pure (name, body)

funDef :: Parser (Id, Expr)
funDef = do
  (name, params) <- parens (liftM2 (,) ident (spaces1 *> sepEndBy1 ident spaces1))
  spaces1
  body <- expr
  pure (name, foldr Lam body params)

expr :: Parser Expr
expr = choice [unit, double, int, str, bool, var, pexpr]

unit :: Parser Expr
unit = try (string "unit" <* notFollowedBy identRest) $> Unit

double, int :: Parser Expr
double = do
  l <- try (option "" (string "-") <++> uintS <++> string ".")
  r <- uintS
  e <- option "" (char 'e' <:> intS)
  pure ((Double . read . concat) [l, r, e])
int = fmap (Int . read) intS
intS = try (option "" (string "-") <++> uintS)
uintS = many1 digit

str :: Parser Expr
str = do
  char '"'
  s <- many (escaped <|> fmap pure (noneOf ['"']))
  char '"'
  pure (Str (concat s))
  where
    escaped :: Parser String
    escaped = do
      char '\\'
      c <- anyChar
      return ['\\', c]

bool :: Parser Expr
bool = try ((<*) ((<|>) (string "true" $> Bool True)
                        (string "false" $> Bool False))
                 (notFollowedBy identRest))

var :: Parser Expr
var = fmap Var ident

pexpr :: Parser Expr
pexpr = parens (choice [if', lam, let', app])

app :: Parser Expr
app = do
  rator <- expr
  rands <- many1 (spaces1 >> expr)
  pure (foldl App rator rands)

if' :: Parser Expr
if' = do
  try (string "if" *> spaces1)
  pred <- expr
  spaces1
  conseq <- expr
  spaces1
  alt <- expr
  pure (If pred conseq alt)

lam :: Parser Expr
lam = do
  try (string "lambda" *> spaces1)
  params <- parens (sepEndBy1 ident spaces1)
  spaces1
  body <- expr
  pure (foldr Lam body params)

let' :: Parser Expr
let' = do
  try (string "let" >> spaces1)
  bindings <- parens (sepEndBy binding spaces)
  spaces1
  body <- expr
  pure (Let bindings body)
  where
    binding = parens (liftM2 (,) ident (spaces1 *> expr))

ident :: Parser Id
ident = fmap Id (identFirst <:> many identRest)

identFirst = letter <|> symbol
identRest = identFirst <|> digit
symbol = satisfy (\c -> and [ any ($ c) [isMark, isPunctuation, isSymbol]
                            , not (elem c "()[]{}")
                            , not (c == '"') ])

(<:>) :: Parser a -> Parser [a] -> Parser [a]
(<:>) = liftM2 (:)

(<++>) :: Parser [a] -> Parser [a] -> Parser [a]
(<++>) = liftM2 (++)

spaces1 :: Parser ()
spaces1 = skipMany1 space

-- Note that () and [] can be used interchangeably, as long as the
-- opening and closing bracket matches.
parens :: Parser a -> Parser a
parens p = choice (map (\(l, r) -> between (char l >> spaces) (spaces >> char r) p)
                       [('(', ')'), ('[', ']')])
