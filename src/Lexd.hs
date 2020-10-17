{-# LANGUAGE LambdaCase, TypeSynonymInstances, FlexibleInstances
           , MultiParamTypeClasses, KindSignatures, DataKinds
           , DeriveDataTypeable #-}

module Lexd where

import SrcPos

data Const
    = Int Int
    | F64 Double
    | Str String
    deriving (Show, Eq)

data Keyword
    = Kcolon | Kdot
    | Kforall | KFun | KBox
    | Kdefine | KdefineColon
    | Kimport | Kextern | Kdata
    | Kfmatch | Kmatch | Kcase
    | Kif | Kfun
    | Klet1 | Klet | Kletrec
    | Ksizeof
    | KidAt | KIdAt
    deriving (Eq, Show)

data TokenTree'
    = Lit Const
    | Small String
    | Big String
    | Keyword Keyword
    | Parens [TokenTree]
    | Brackets [TokenTree]
    | Braces [TokenTree]
    deriving (Show)

type TokenTree = WithPos TokenTree'
