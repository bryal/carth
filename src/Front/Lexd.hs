{-# LANGUAGE DataKinds #-}

module Front.Lexd where

import Front.SrcPos

data Const
    = Int Int
    | F64 Double
    | Str String
    deriving (Show, Eq)

data Keyword
    = Kcolon | Kdot
    | Kforall | Kwhere | KFun | KBox
    | Kdefine | KdefineColon
    | Kimport | Kextern | Kdata
    | Kmatch | Kcase
    | Kif | Kfun | KfunStar
    | Klet1 | Klet | Kletrec
    | Ksizeof
    | KidAt | KIdAt
    | Kdefmacro
    deriving (Eq, Show)

data TokenTree'
    = Lit Const
    | Small String
    | Big String
    | Keyword Keyword
    | Parens [TokenTree]
    | Brackets [TokenTree]
    | Braces [TokenTree]
    | Ellipsis TokenTree
    deriving (Eq, Show)

type TokenTree = WithPos TokenTree'
