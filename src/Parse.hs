{-# LANGUAGE FlexibleContexts, LambdaCase, TupleSections #-}

module Parse (parse, reserveds) where

import Control.Monad
import Data.Char (isMark, isPunctuation, isSymbol, isUpper)
import Data.Functor
import Data.Maybe
import Control.Applicative (liftA2)
import qualified Text.Megaparsec as Parsec
import Text.Megaparsec hiding (parse, match)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as Lexer
import Data.Scientific (floatingOrInteger)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Either.Combinators
import Data.Void
import Data.Composition

import Misc
import Ast
import NonEmpty

type Parser = Parsec Void String

type SourceName = String

parse :: SourceName -> String -> Either String Program
parse = parse' program

parse' :: Parser a -> SourceName -> String -> Either String a
parse' p name src = mapLeft errorBundlePretty (Parsec.parse p name src)

program :: Parser Program
program = do
    space
    (defs, typedefs) <- toplevels
    eof
    main <- maybe
        (fail "main function not defined")
        pure
        (lookup (Id "main") defs)
    pure (Program main (filter ((/= (Id "main")) . fst) defs) typedefs)

toplevels :: Parser ([Def], [TypeDef])
toplevels = option ([], []) (toplevel >>= flip fmap toplevels)

toplevel :: Parser (([Def], [TypeDef]) -> ([Def], [TypeDef]))
toplevel =
    parens $ choice [fmap (mapSnd . (:)) typedef, fmap (mapFst . (:)) def]

typedef :: Parser TypeDef
typedef = do
    _ <- reserved "type"
    let onlyName = fmap (, []) big
    let nameAndMany1 = parens . liftA2 (,) big . many1
    (name, params) <- onlyName <|> nameAndMany1 small'
    constrs <- many (onlyName <|> nameAndMany1 type')
    pure (TypeDef name params (ConstructorDefs (Map.fromList constrs)))

def :: Parser Def
def = defUntyped <|> defTyped

defUntyped :: Parser Def
defUntyped = reserved "define" *> def' (pure Nothing)

defTyped :: Parser Def
defTyped = reserved "define:" *> def' (fmap Just scheme)

def'
    :: Parser (Maybe (WithPos Scheme))
    -> Parser (Id, (Maybe (WithPos Scheme), Expr))
def' schemeParser = varDef <|> funDef
  where
    varDef = do
        name <- small'
        scm <- schemeParser
        body <- expr
        pure (name, (scm, body))
    funDef = do
        (name, params) <- parens (liftM2 (,) small' (many1 (withPos small')))
        scm <- schemeParser
        body <- expr
        let
            fun =
                foldr (\(WithPos pos p) b -> WithPos pos (Fun p b)) body params
        pure (name, (scm, fun))

expr :: Parser Expr
expr =
    withPos $ choice [unit, charLit, str, bool, var, num, eConstructor, pexpr]

unit :: Parser Expr'
unit = reserved "unit" $> Lit Unit

num :: Parser Expr'
num = lexeme $ fmap
    (Lit . either Double Int . floatingOrInteger)
    (Lexer.signed nop Lexer.scientific)

charLit :: Parser Expr'
charLit = lexeme
    $ fmap (Lit . Char) (between (char '\'') (char '\'') Lexer.charLiteral)

str :: Parser Expr'
str = lexeme
    $ fmap (Lit . Str) (char '"' >> manyTill Lexer.charLiteral (char '"'))

bool :: Parser Expr'
bool = do
    b <- (reserved "true" $> True) <|> (reserved "false" $> False)
    pure (Lit (Bool b))

var :: Parser Expr'
var = fmap Var small'

eConstructor :: Parser Expr'
eConstructor = fmap Constructor big

pexpr :: Parser Expr'
pexpr = parens (choice [funMatch, match, if', fun, let', typeAscr, app])

funMatch :: Parser Expr'
funMatch = reserved "fun-match" *> fmap FunMatch cases

match :: Parser Expr'
match = do
    reserved "match"
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

app :: Parser Expr'
app = do
    rator <- expr
    rands <- many1 expr
    pure (unpos (foldl (WithPos (getPos rator) .* App) rator rands))

if' :: Parser Expr'
if' = do
    reserved "if"
    pred <- expr
    conseq <- expr
    alt <- expr
    pure (If pred conseq alt)

fun :: Parser Expr'
fun = do
    reserved "fun"
    params <- choice
        [parens (many1 (withPos small')), fmap (\x -> [x]) (withPos small')]
    body <- expr
    pure $ unpos
        (foldr (\(WithPos pos p) b -> WithPos pos (Fun p b)) body params)


let' :: Parser Expr'
let' = do
    reserved "let"
    bindings <- parens (many1' binding)
    body <- expr
    pure (Let bindings body)

binding :: Parser Def
binding = parens (bindingTyped <|> bindingUntyped)
  where
    bindingTyped =
        reserved ":" *> liftA2 (,) small' (liftA2 (,) (fmap Just scheme) expr)
    bindingUntyped = liftA2 (,) small' (fmap (Nothing, ) expr)

typeAscr :: Parser Expr'
typeAscr = reserved ":" *> liftA2 TypeAscr expr type'

scheme :: Parser (WithPos Scheme)
scheme = withPos $ wrap nonptype <|> parens (universal <|> wrap ptype')
  where
    wrap = fmap (Forall Set.empty)
    universal = reserved "forall" *> liftA2 Forall tvars type'
    tvars = parens (fmap Set.fromList (many tvar))

type' :: Parser Type
type' = nonptype <|> ptype

nonptype :: Parser Type
nonptype = choice [fmap TPrim tprim, fmap TVar tvar, fmap (flip TConst []) big]

ptype :: Parser Type
ptype = parens ptype'

ptype' :: Parser Type
ptype' = tfun <|> tapp

tapp :: Parser Type
tapp = liftA2 TConst big (many1 type')

tfun :: Parser Type
tfun = do
    reserved "Fun"
    t <- type'
    ts <- many1 type'
    pure (foldr1 TFun (t : ts))

tprim :: Parser TPrim
tprim = try $ do
    s <- big
    case s of
        "Unit" -> pure TUnit
        "Int" -> pure TInt
        "Double" -> pure TDouble
        "Char" -> pure TChar
        "Str" -> pure TStr
        "Bool" -> pure TBool
        _ -> fail $ "Undefined type constant " ++ s

tvar :: Parser TVar
tvar = fmap TVExplicit small'

-- Note that () and [] can be used interchangeably, as long as the
-- opening and closing bracket matches.
parens :: Parser a -> Parser a
parens p = choice
    (map (($ p) . uncurry between . both symbol) [("(", ")"), ("[", "]")])


big :: Parser String
big = try $ do
    s <- identifier
    let c = head s
    if (isUpper c || [c] == ":")
        then pure s
        else fail "Big identifier must start with an uppercase letter or colon."

small' :: Parser Id
small' = fmap Id small

small :: Parser String
small = try $ do
    s <- identifier
    let c = head s
    if (isUpper c || [c] == ":")
        then
            fail
                "Small identifier must not start with an uppercase letter or colon."
        else pure s

identifier :: Parser String
identifier = do
    name <- ident
    if elem name reserveds
        then unexpected (Label (toList1 ("reserved word " ++ show name)))
        else pure name

ident :: Parser String
ident = lexeme $ label "identifier" $ liftA2 (:) identStart (many identLetter)

identStart :: Parser Char
identStart =
    choice [letterChar, otherChar, try (oneOf "-+" <* notFollowedBy digitChar)]

identLetter :: Parser Char
identLetter = letterChar <|> otherChar <|> oneOf "-+" <|> digitChar

reserved :: String -> Parser ()
reserved x = do
    if not (elem x reserveds)
        then ice ("`" ++ x ++ "` is not a reserved word")
        else label ("reserved word " ++ x) (try (mfilter (== x) ident)) $> ()

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme space

symbol :: String -> Parser String
symbol = Lexer.symbol space

reserveds :: [String]
reserveds =
    [ ":"
    , "Fun"
    , "define"
    , "define:"
    , "forall"
    , "unit"
    , "true"
    , "false"
    , "fun-match"
    , "match"
    , "if"
    , "fun"
    , "let"
    , "type"
    ]

otherChar :: Parser Char
otherChar = satisfy
    (\c -> and
        [ any ($ c) [isMark, isPunctuation, isSymbol]
        , not (elem c "()[]{}")
        , not (elem c "\"-+")
        ]
    )

many1' :: Parser a -> Parser (NonEmpty a)
many1' = fmap (fromJust . nonEmpty) . many1

many1 :: Parser a -> Parser [a]
many1 p = liftA2 (:) p (many p)

nop :: Parser ()
nop = pure ()

withPos :: Parser a -> Parser (WithPos a)
withPos = liftA2 WithPos getSourcePos
