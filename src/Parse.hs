{-# LANGUAGE FlexibleContexts #-}

module Parse where

import Control.Monad
import Data.Char (isMark, isPunctuation, isSymbol)
import Data.Either.Combinators (rightToMaybe)
import Data.List (intercalate)
import Data.Functor
import Text.Parsec

type Ident = String

data Expr
  = Nil
  | Int Int
  | Double Double
  | Str String
  | Bool Bool
  | Var Ident
  | App Expr Expr
  | If Expr Expr Expr
  | Lam Ident Expr
  | Let [(Ident, Expr)] Expr
  | New Ident [Expr]
  deriving (Show, Eq)

type Parser = Parsec String ()

expr :: Parser Expr
expr = choice [nil, double, int, str, bool, var, pexpr]

nil :: Parser Expr
nil = string "nil" $> Nil

double :: Parser Expr
double = fmap (Double . read) (intS <++> (char '.' <:> intS))

int :: Parser Expr
int = fmap (Int . read) intS

intS :: Parser String
intS = many1 digit

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
bool = (string "true" $> Bool True) <|> (string "false" $> Bool False)

var :: Parser Expr
var = fmap Var ident

pexpr :: Parser Expr
pexpr = parens (choice [app, if', lam, let', new])

app :: Parser Expr
app = do
  rator <- expr
  rands <- many1 (spaces1 >> expr)
  pure (foldl App rator rands)

if' :: Parser Expr
if' = do
  string "if"
  spaces1
  pred <- expr
  spaces1
  conseq <- expr
  spaces1
  alt <- expr
  pure (If pred conseq alt)

lam :: Parser Expr
lam = do
  string "lambda"
  spaces1
  params <- parens (sepEndBy1 ident spaces1)
  spaces1
  body <- expr
  pure (foldr Lam body params)

let' :: Parser Expr
let' = do
  string "let"
  spaces1
  bindings <- parens (sepEndBy binding spaces)
  spaces1
  body <- expr
  pure (Let bindings body)
  where
    binding = parens (liftM2 (,) ident (spaces1 *> expr))

new :: Parser Expr
new = do
  string "new"
  spaces1
  variant <- ident
  spaces1
  members <- sepEndBy1 expr spaces1
  pure (New variant members)

ident :: Parser Ident
ident = identFirst <:> many identRest
  where
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

parens :: Parser a -> Parser a
parens = between (char '(' >> spaces) (spaces >> char ')')



--- Tests

type Test = (String, String, Parsec String () String, Maybe String)

printTestResults = putStrLn prettyTestResults

prettyTestResults =
  let pretty (Right name) = mconcat ["Test `", name, "` passed!"]
      pretty (Left (name, found, expected)) =
        mconcat [ "Test `"
                , name
                , "` failed!\n"
                , "  Expected "
                , case expected of
                    Just s -> "successful parse of\n    `" ++ s ++ "`"
                    Nothing -> "failed parse"
                , "\n  found\n    "
                , show found ]
  in intercalate "\n" (map pretty testResults)

testResults = map runTest tests

runTest (name, input, parser, expected) =
  let result = (parse parser name input)
  in if rightToMaybe result == expected
       then Right name
       else (Left (name, result, expected))


tests = [tNil, tInt, tFloat, tBool, tVar, tStr, tApp, tIf, tLam, tLet, tNew]

tNil, tInt, tFloat, tStr, tBool, tVar, tApp, tIf, tLam, tLet, tNew :: Test

tNil = ("parse nil", "nil", fmap show nil, Just (show Nil))
tInt = ("parse int", "123", fmap show int, Just (show (Int 123)))
tFloat = ("parse double", "123.456", fmap show double, Just (show (Double 123.456)))
tStr = ( "parse string"
       , "\"Hello, \\\"World!\\\"\""
       , fmap show str
       , Just (show (Str "Hello, \\\"World!\\\"")))
tBool = ( "parse bool"
        , "true false"
        , fmap show (sepBy bool (char ' '))
        , Just (show [Bool True, Bool False]))
tVar = ("parse variable", "_m�in-1", fmap show var, Just (show (Var "_m�in-1")))
tApp = ( "parse app"
       , "(++ \"Hello\" \" World!\")"
       , fmap show app
       , Just (show (App (App (Var "++") (Str "Hello")) (Str " World!"))))
tIf = ( "parse if"
      , "(if (= a b) 0 (+ x y))"
      , fmap show if'
      , Just (show (If (App (App (Var "=") (Var "a")) (Var "b"))
                       (Int 0)
                       (App (App (Var "+") (Var "x")) (Var "y")))))
tLam = ( "parse lambda"
       , "(lambda (a b) (+ a b))"
       , fmap show lam
       , Just (show (Lam "a" (Lam "b" (App (App (Var "+") (Var "a")) (Var "b"))))))
tLet = ( "parse let"
       , "(let ((a 1)(b 0)) (+ a b))"
       , fmap show let'
       , Just (show (Let [("a", Int 1), ("b", Int 0)]
                         (App (App (Var "+") (Var "a")) (Var "b")))))
tNew = ( "parse new"
       , "(new Pair a 1.0)"
       , fmap show new
       , Just (show (New "Pair" [Var "a", Double 1.0])))
