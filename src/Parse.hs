{-# LANGUAGE FlexibleContexts, LambdaCase #-}

module Parse (parse) where

import NonEmpty
import Ast
import Control.Monad
import Data.Maybe
import Data.Composition
import Data.Char (isMark, isPunctuation, isSymbol)
import Data.Functor
import qualified Data.Map.Strict as Map
import qualified Text.Parsec as Parsec
import Text.Parsec hiding (parse)

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
  pure (name, foldr Fun body params)

expr :: Parser Expr
expr = choice [unit, double, int, charLit, str, bool, var, eConstructor, pexpr]

unit :: Parser Expr
unit = try (string "unit" <* notFollowedBy identRest) $> Unit

double, int :: Parser Expr
double = do
  l <- try (option "" (string "-") <++> uintS <++> string ".")
  r <- uintS
  e <- option "" (char 'e' <:> intS)
  pure ((Double . read . concat) [l, r, e])
int = fmap (Int . read) intS

intS, uintS :: Parser String
intS = try (option "" (string "-") <++> uintS)
uintS = many1 digit

charLit :: Parser Expr
charLit = char '\'' *> fmap Char (escaped <|> anyChar) <* char '\''

str :: Parser Expr
str = do
  char '"'
  s <- many (escaped <|> noneOf ['"'])
  char '"'
  pure (Str s)

escaped :: Parser Char
escaped = do
  char '\\'
  c <- choice (map char ['0', 'a', 'b', 't', 'n', 'v', 'f', 'r', '\\', '\"'])
  return (escapeChar c)
  where escapeChar = \case
          '0' -> '\0'
          'a' -> '\a'
          'b' -> '\b'
          't' -> '\t'
          'n' -> '\n'
          'v' -> '\v'
          'f' -> '\f'
          'r' -> '\r'
          '\\' -> '\\'
          '\"' -> '"'
          c -> error ("ICE: Unknown escape character \'" ++ c : "\'")

bool :: Parser Expr
bool = try ((<*) ((<|>) (string "true" $> Bool True)
                        (string "false" $> Bool False))
                 (notFollowedBy identRest))

var :: Parser Expr
var = fmap Var ident

eConstructor :: Parser Expr
eConstructor = fmap Constructor constructor

pexpr :: Parser Expr
pexpr = parens (choice [funMatch, match, if', fun, let', app])

funMatch :: Parser Expr
funMatch = try (string "fun-match" *> spaces1) *> fmap FunMatch cases

match :: Parser Expr
match = do
  try (string "match" *> spaces1)
  e <- expr
  spaces1
  cs <- cases
  pure (Match e cs)

cases :: Parser (NonEmpty (Pat, Expr))
cases = sepEndBy1' case' spaces1

case' :: Parser (Pat, Expr)
case' = parens (liftM2 (,) pat (spaces1 *> expr))

pat :: Parser Pat
pat = patTor <|> patTion <|> patVar
  where patTor = fmap PConstructor constructor
        patTion = parens (liftM2 PConstruction constructor (spaces1 *> sepEndBy1' pat spaces1))
        patVar = fmap PVar ident

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

fun :: Parser Expr
fun = do
  try (string "fun" *> spaces1)
  params <- parens (sepEndBy1 ident spaces1)
  spaces1
  body <- expr
  pure (foldr Fun body params)

let' :: Parser Expr
let' = do
  try (string "let" >> spaces1)
  bindings <- parens (sepEndBy1' binding spaces)
  spaces1
  body <- expr
  pure (Let bindings body)
  where
    binding = parens (liftM2 (,) ident (spaces1 *> expr))

ident :: Parser Id
ident = fmap Id (identFirst <:> many identRest)
  where identFirst = lower <|> symbol

constructor :: Parser String
constructor = constructorFirst <:> many identRest
  where constructorFirst = upper <|> char ':'

identRest :: Parser Char
identRest = letter <|> symbol <|> digit

symbol :: Parser Char
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

sepEndBy1' :: Stream s m t => ParsecT s u m a -> ParsecT s u m sep -> ParsecT s u m (NonEmpty a)
sepEndBy1' = fmap (fromJust . nonEmpty) .* sepEndBy1
