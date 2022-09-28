{-# LANGUAGE DataKinds #-}

module Front.Lexd where

import Front.SrcPos

data Const
    = Int Int
    | F64 Double
    | Str String
    deriving (Show, Eq)

data Reserved
    = Rcolon
    | Rdot
    | Rforall
    | Rwhere
    | RFun
    | RBox
    | Rdefun
    | Rdef
    | Rimport
    | Rextern
    | Rdata
    | Rmatch
    | Rcase
    | Rif
    | Rfun
    | Rlet1
    | Rlet
    | Rletrec
    | Rsizeof
    | Rdefmacro
    | Rtype
    deriving (Eq, Show)

data TokenTree'
    = Reserved Reserved
    | Keyword String
    | Lit Const
    | Small String
    | Big String
    | Parens [TokenTree]
    | Brackets [TokenTree]
    | Braces [TokenTree]
    | Backslashed TokenTree
    | Octothorped TokenTree
    | Octothorpe
    | Ellipsis TokenTree
    deriving (Eq, Show)

type TokenTree = WithPos TokenTree'
