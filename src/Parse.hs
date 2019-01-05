{-# LANGUAGE FlexibleContexts #-}

module Parse where

import Control.Monad
import Data.Char (isMark, isPunctuation, isSymbol)
import Data.Either.Combinators (rightToMaybe)
import Data.List (intercalate)
import Text.Parsec

data Expr
  = Nil
  | Num String
  | Str String
  | Bool Bool
  | Var String
  | App Expr Expr
  | If Expr Expr Expr
  | Lam String Expr
  | Let [(String, Expr)] Expr
  | New String [Expr]
  deriving (Show, Eq)

expr = choice [nil, num, str, bool, var, app, if', lam, let', new]

nil = fmap (const Nil) (string "nil")

num = fmap Num (many1 digit <++> option "" (char '.' <:> many1 digit))

str = do
  char '"'
  s <- many (escaped <|> (fmap (\c -> [c]) (noneOf ['"'])))
  char '"'
  return (Str (concat s))
  where
    escaped :: Parsec String () String
    escaped = do
      char '\\'
      c <- anyChar
      return ['\\', c]

bool :: Parsec String u Expr
bool = fmap Bool (fmap (const True) (string "true") <|> fmap (const False) (string "false"))

var = fmap Var ident

app = parens (do rator <- expr
                 rands <- many1 (spaces1 >> expr)
                 return (foldl App rator rands))

if' = parens (do string "if"
                 spaces1
                 pred <- expr
                 spaces1
                 conseq <- expr
                 spaces1
                 alt <- expr
                 return (If pred conseq alt))

lam = parens (do string "lambda"
                 spaces1
                 params <- (parens (sepEndBy1 ident spaces1))
                 spaces1
                 body <- expr
                 return (foldr Lam body params))

let' = let bindings = (parens ((>>) spaces (sepEndBy binding spaces)))
           binding = (parens (liftM2 (,) ident ((>>) spaces1 expr)))
       in parens (do string "let"
                     spaces1
                     binds <- bindings
                     spaces1
                     body <- expr
                     return (Let binds body))

new = parens (do string "new"
                 spaces1
                 variant <- ident
                 spaces1
                 members <- (sepEndBy1 expr spaces1)
                 return (New variant members))

ident = identFirst <:> many identRest

identFirst = letter <|> symbol

identRest = identFirst <|> digit

symbol = satisfy (\c -> and [ any (\pred -> pred c) [isMark, isPunctuation, isSymbol]
                            , not (isBracket c)
                            , not (c == '"') ])

isBracket c = elem c "()[]{}"

(<:>) = liftM2 (:)

(<++>) = liftM2 (++)

spaces1 = skipMany1 space

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
tInt = ("parse integer", "123", fmap show num, Just (show (Num "123")))
tFloat = ("parse float", "123.456", fmap show num, Just (show (Num "123.456")))
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
                       (Num "0")
                       (App (App (Var "+") (Var "x")) (Var "y")))))
tLam = ( "parse lambda"
       , "(lambda (a b) (+ a b))"
       , fmap show lam
       , Just (show (Lam "a" (Lam "b" (App (App (Var "+") (Var "a")) (Var "b"))))))
tLet = ( "parse let"
       , "(let ((a 1)(b 0)) (+ a b))"
       , fmap show let'
       , Just (show (Let [("a", Num "1"), ("b", Num "0")]
                         (App (App (Var "+") (Var "a")) (Var "b")))))
tNew = ( "parse new"
       , "(new Pair a 1)"
       , fmap show new
       , Just (show (New "Pair" [Var "a", Num "1"])))
