module Parse where

import Text.Parsec
import Data.Char (isMark, isPunctuation, isSymbol)

(<:>) p q = do
  a <- p
  as <- q
  return (a:as)

and' a b = a && b

isBracket c = elem c "()[]{}"

symbol = satisfy (\c -> and' (any (\pred -> pred c)
                                  [isMark, isPunctuation, isSymbol])
                             (not (isBracket c)))

identFirstChar = letter <|> symbol
identRestChar = identFirstChar <|> digit
ident = identFirstChar <:> many identRestChar

sIdent = "_mäin-1"
pIdent = parse ident "<test>" sIdent
-- src = "(define main (display \"Hello, World!\"))"

