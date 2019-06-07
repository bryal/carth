{-# LANGUAGE FlexibleContexts, LambdaCase, TupleSections #-}

module Parse (parse) where

import Control.Monad
import Data.Char (isMark, isPunctuation, isSymbol, isUpper)
import Data.Functor
import Data.Functor.Identity
import Data.Maybe
import Control.Applicative (liftA2)
import qualified Text.Parsec as Parsec
import Text.Parsec hiding (parse)
import qualified Text.Parsec.Token as Token
import qualified Data.Set as Set

import Ast
import NonEmpty

type Parser = Parsec String ()

parse :: SourceName -> String -> Either ParseError Program
parse = Parsec.parse program

program :: Parser Program
program = do
    spaces
    defs <- many1 def
    eof
    main <- maybe
        (fail "main function not defined")
        pure
        (lookup (Id "main") defs)
    pure (Program main (filter ((/= (Id "main")) . fst) defs))

def :: Parser (Id, (Maybe Scheme, Expr))
def = parens (defUntyped <|> defTyped)

defUntyped :: Parser (Id, (Maybe Scheme, Expr))
defUntyped = try (reserved "define") *> (varDef <|> funDef)
  where
    varDef = do
        name <- small'
        body <- expr
        pure (name, (Nothing, body))
    funDef = do
        (name, params) <- parens (liftM2 (,) small' (many1 small'))
        body <- expr
        pure (name, (Nothing, foldr Fun body params))

defTyped :: Parser (Id, (Maybe Scheme, Expr))
defTyped = try (reserved "define:") *> (varDef <|> funDef)
  where
    varDef = do
        name <- small'
        scm <- scheme
        body <- expr
        pure (name, (Just scm, body))
    funDef = do
        (name, params) <- parens (liftM2 (,) small' (many1 small'))
        scm <- scheme
        body <- expr
        pure (name, (Just scm, foldr Fun body params))

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
var = fmap Var small'

eConstructor :: Parser Expr
eConstructor = fmap Constructor big

pexpr :: Parser Expr
pexpr = parens (choice [funMatch, match, if', fun, let', typeAscr, app])

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
    patTor = fmap PConstructor big
    patTion = parens (liftM2 PConstruction big (many1' pat))
    patVar = fmap PVar small'

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
    params <- choice [parens (many1 small'), fmap (\x -> [x]) small']
    body <- expr
    pure (foldr Fun body params)

let' :: Parser Expr
let' = do
    try (reserved "let")
    bindings <- parens (many1' binding)
    body <- expr
    pure (Let bindings body)

binding :: Parser (Id, (Maybe Scheme, Expr))
binding = parens (bindingTyped <|> bindingUntyped)
  where
    bindingTyped =
        reserved ":" *> liftA2 (,) small' (liftA2 (,) (fmap Just scheme) expr)
    bindingUntyped = liftA2 (,) small' (fmap (Nothing, ) expr)

typeAscr :: Parser Expr
typeAscr = try (reserved ":") *> liftA2 TypeAscr expr type'

scheme :: Parser Scheme
scheme = wrap nonptype <|> parens (universal <|> wrap ptype')
  where
    wrap = fmap (Forall Set.empty)
    universal = try (reserved "forall") *> liftA2 Forall tvars type'
    tvars = parens (fmap Set.fromList (many tvar))

type' :: Parser Type
type' = nonptype <|> ptype

nonptype :: Parser Type
nonptype = choice [fmap TConst tconst, fmap TVar tvar]

ptype :: Parser Type
ptype = parens ptype'

ptype' :: Parser Type
ptype' = tfun

tfun :: Parser Type
tfun = do
    try (reserved "Fun")
    t <- type'
    ts <- many1 type'
    pure (foldr1 TFun (t : ts))

tconst :: Parser TConst
tconst = try $ do
    s <- Token.identifier lexer
    let c = head s
    when (not (isUpper c))
        $ fail "Type-name must start with an uppercase letter."
    case s of
        "Unit" -> pure TUnit
        "Int" -> pure TInt
        "Double" -> pure TDouble
        "Char" -> pure TChar
        "Str" -> pure TStr
        "Bool" -> pure TBool
        _ -> fail $ "Undefined type constant " ++ s

tvar :: Parser TVar
tvar = fmap TVExplicit small

-- Note that () and [] can be used interchangeably, as long as the
-- opening and closing bracket matches.
parens :: Parser a -> Parser a
parens p = choice (map (($ p) . ($ lexer)) [Token.parens, Token.brackets])

big :: Parser String
big = try $ do
    s <- Token.identifier lexer
    let c = head s
    if (isUpper c || [c] == ":")
        then pure s
        else fail "Big identifier must start with an uppercase letter or colon."

small' :: Parser Id
small' = fmap Id small

small :: Parser String
small = try $ do
    s <- Token.identifier lexer
    let c = head s
    if (isUpper c || [c] == ":")
        then
            fail
                "Small identifier must not start with an uppercase letter or colon."
        else pure s

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
