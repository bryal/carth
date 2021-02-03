-- | This module mostly exists to expost the builtin types via convenient variables,
--   instead of requiring redefinitions or manually typing the strings of TConst's, which
--   would be prone to typo errors.
module TypeAst where

import Data.Word

data TPrim
    = TNat Word32
    | TNatSize
    | TInt Word32
    | TIntSize
    | TF16
    | TF32
    | TF64
    | TF128
    deriving (Show, Eq, Ord)

type TConst t = (String, [t])

class TypeAst t where
    tprim :: TPrim -> t
    tconst :: TConst t -> t
    tfun :: t -> t -> t
    tbox :: t -> t

mainType :: TypeAst t => t
mainType = tIO tUnit

tIO :: TypeAst t => t -> t
tIO a = tconst ("IO", [a])

tByte :: TypeAst t => t
tByte = tprim (TNat 8)

tBox' :: t -> TConst t
tBox' t = ("Box", [t])

tStr :: TypeAst t => t
tStr = tconst tStr'

tStr' :: TConst t
tStr' = ("Str", [])

tArray :: TypeAst t => t -> t
tArray a = tconst ("Array", [a])

tTuple :: TypeAst t => [t] -> t
tTuple = foldr tCons tUnit

tCons :: TypeAst t => t -> t -> t
tCons car cdr = tconst ("Cons", [car, cdr])

tRealWorld :: TypeAst t => t
tRealWorld = tconst ("RealWorld", [])

tUnit :: TypeAst t => t
tUnit = tconst tUnit'

tUnit' :: TConst t
tUnit' = ("Unit", [])

tBool :: TypeAst t => t
tBool = tconst ("Bool", [])

tBool' :: TConst t
tBool' = ("Bool", [])
