{-# LANGUAGE FlexibleContexts, LambdaCase #-}

module Parse (parse) where

import Ast
import Control.Monad
import Data.Char (isMark, isPunctuation, isSymbol, isUpper)
import Data.Functor
import Data.Functor.Identity
import Data.Maybe
import NonEmpty
import qualified Text.Parsec as Parsec
import Text.Parsec hiding (parse)
import qualified Text.Parsec.Token as Token

type Parser = Parsec String ()

parse :: SourceName -> String -> Either ParseError Program
parse = Parsec.parse program

program :: Parser Program
program = do
    defs <- many1 def
    eof
    main <- maybe
        (fail "main function not defined")
        pure
        (lookup (Id "main") defs)
    pure (Program main (filter ((/= (Id "main")) . fst) defs))

def :: Parser (Id, Expr)
def = parens (reserved "define" *> (varDef <|> funDef))

varDef :: Parser (Id, Expr)
varDef = do
    name <- ident
    body <- expr
    pure (name, body)

funDef :: Parser (Id, Expr)
funDef = do
    (name, params) <- parens (liftM2 (,) ident (many1 ident))
    body <- expr
    pure (name, foldr Fun body params)

expr :: Parser Expr
expr = choice [unit, charLit, str, bool, var, num, eConstructor, pexpr]

unit :: Parser Expr
unit = try (reserved "unit") $> Lit Unit

num :: Parser Expr
num = do
    neg <- option False (char '-' $> True)
    a <- Token.naturalOrFloat lexer
    let
        e = either
            (\n -> Int (fromInteger (if neg then -n else n)))
            (\x -> Double (if neg then -x else x))
            a
    pure (Lit e)

charLit :: Parser Expr
charLit = fmap (Lit . Char) (Token.charLiteral lexer)

str :: Parser Expr
str = fmap (Lit . Str) (Token.stringLiteral lexer)

bool :: Parser Expr
bool = do
    b <- try ((reserved "true" $> True) <|> (reserved "false" $> False))
    pure (Lit (Bool b))

var :: Parser Expr
var = fmap Var ident

eConstructor :: Parser Expr
eConstructor = fmap Constructor constructor

pexpr :: Parser Expr
pexpr = parens (choice [funMatch, match, if', fun, let', app])

funMatch :: Parser Expr
funMatch = try (reserved "fun-match") *> fmap FunMatch cases

match :: Parser Expr
match = do
    try (reserved "match")
    e <- expr
    cs <- cases
    pure (Match e cs)

cases :: Parser (NonEmpty (Pat, Expr))
cases = many1' case'

case' :: Parser (Pat, Expr)
case' = parens (liftM2 (,) pat expr)

pat :: Parser Pat
pat = patTor <|> patTion <|> patVar
  where
    patTor = fmap PConstructor constructor
    patTion = parens (liftM2 PConstruction constructor (many1' pat))
    patVar = fmap PVar ident

app :: Parser Expr
app = do
    rator <- expr
    rands <- many1 expr
    pure (foldl App rator rands)

if' :: Parser Expr
if' = do
    try (reserved "if")
    pred <- expr
    conseq <- expr
    alt <- expr
    pure (If pred conseq alt)

fun :: Parser Expr
fun = do
    try (reserved "fun")
    params <- parens (many1 ident)
    body <- expr
    pure (foldr Fun body params)

let' :: Parser Expr
let' = do
    try (reserved "let")
    bindings <- parens (many1' binding)
    body <- expr
    pure (Let bindings body)
    where binding = parens (liftM2 (,) ident expr)

-- Note that () and [] can be used interchangeably, as long as the
-- opening and closing bracket matches.
parens :: Parser a -> Parser a
parens p = choice (map (($ p) . ($ lexer)) [Token.parens, Token.brackets])

constructor :: Parser String
constructor = try $ do
    s <- Token.identifier lexer
    let c = head s
    if (isUpper c || [c] == ":")
        then pure s
        else fail "Constructor must start with an uppercase letter or colon."

ident :: Parser Id
ident = try $ do
    s <- Token.identifier lexer
    let c = head s
    if (isUpper c || [c] == ":")
        then fail "Identifier must not start with an uppercase letter or colon."
        else pure (Id s)

reserved :: String -> Parser ()
reserved = Token.reserved lexer

lexer :: Token.GenTokenParser String () Identity
lexer = Token.makeTokenParser langDef

langDef :: Token.LanguageDef ()
langDef = Token.LanguageDef
    { Token.commentStart = ";{"
    , Token.commentEnd = ";}"
    , Token.commentLine = ";"
    , Token.nestedComments = True
    , Token.opStart = parserZero
    , Token.opLetter = parserZero
    , Token.reservedOpNames = []
    , Token.identStart = choice
        [letter, symbol, try (oneOf "-+" <* notFollowedBy digit)]
    , Token.identLetter = letter <|> symbol <|> oneOf "-+" <|> digit
    , Token.reservedNames = reserveds
    , Token.caseSensitive = True
    }

symbol :: Parsec String () Char
symbol = satisfy
    (\c -> and
        [ any ($ c) [isMark, isPunctuation, isSymbol]
        , not (elem c "()[]{}")
        , not (elem c "\"-+")
        ]
    )

many1' :: Stream s m t => ParsecT s u m a -> ParsecT s u m (NonEmpty a)
many1' = fmap (fromJust . nonEmpty) . many1
