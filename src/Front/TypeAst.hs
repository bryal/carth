-- | This module mostly exists to expost the builtin types via convenient variables,
--   instead of requiring redefinitions or manually typing the strings of TConst's, which
--   would be prone to typo errors.
module Front.TypeAst where

import Data.Word

data TPrim
    = TNat Word32
    | TNatSize
    | TInt Word32
    | TIntSize
    | TF32
    | TF64
    deriving (Show, Eq, Ord)

type TConst' var = (String, [Type' var])

data Type' var
    = TVar var
    | TPrim TPrim
    | TConst (TConst' var)
    | TFun [Type' var] (Type' var)
    | TBox (Type' var)
    deriving (Show, Eq, Ord)

unTconst :: Type' var -> Maybe (TConst' var)
unTconst (TConst tc) = Just tc
unTconst _ = Nothing

mainType :: Type' var
mainType = tIO tUnit

tIO :: Type' var -> Type' var
tIO a = TConst ("IO", [a])

tByte :: Type' var
tByte = TPrim (TNat 8)

tBox' :: Type' var -> TConst' var
tBox' t = ("Box", [t])

tStr :: Type' var
tStr = TConst tStr'

tStr' :: TConst' var
tStr' = ("Str", [])

tArray :: Type' var -> Type' var
tArray a = TConst ("Array", [a])

tUnit :: Type' var
tUnit = TConst tUnit'

tUnit' :: TConst' var
tUnit' = ("Unit", [])

tBool :: Type' var
tBool = TConst ("Bool", [])

tBool' :: TConst' var
tBool' = ("Bool", [])
