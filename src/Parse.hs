module Parse where

import Text.Parsec
import Data.Char (isMark, isPunctuation, isSymbol)

data Expr = Var String
          | Str String
          | App Expr [Expr]
  deriving Show

and' a b = a && b

isBracket c = elem c "()[]{}"

(<:>) p q = do
  a <- p
  as <- q
  return (a:as)

spaces1 = skipMany1 space

symbol = satisfy (\c -> and [ any (\pred -> pred c)
                                  [isMark, isPunctuation, isSymbol]
                            , not (isBracket c)
                            , not (c == '"') ])

identFirstChar = letter <|> symbol
identRestChar = identFirstChar <|> digit
ident = identFirstChar <:> many identRestChar

var = fmap Var ident

escaped :: Parsec String () String
escaped = do
  char '\\'
  c <- anyChar
  return ['\\', c]

str' = do
  char '"'
  s <- many (escaped <|> fmap (\c -> [c]) (noneOf ['"']))
  char '"'
  return (concat s)

str = fmap Str str'

app = do
  char '('
  spaces
  rator <- expr
  rands <- many (spaces1 >> expr)
  spaces
  char ')'
  return (App rator rands)

expr = choice [var, str, app]

sIdent = "_mäin-1"
pIdent = parse ident "" sIdent

sStr = "\"Hello, \\\"World!\\\"\""
pStr = parse str "" sStr

sApp = "(display \"Hello, World!\")"
pApp = parse app "" sApp

-- src = "(define main (display \"Hello, World!\"))"

