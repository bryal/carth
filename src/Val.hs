{-# LANGUAGE LambdaCase #-}

module Val
    ( Val(..)
    , ice
    , unwrapUnit
    , unwrapInt
    , unwrapBool
    , unwrapFun
    ) where

import Ast (Const(..))

data Val
    = VConst Const
    | VFun (Val -> IO Val)

unwrapUnit :: Val -> ()
unwrapUnit =
    \case
        VConst Unit -> ()
        x -> ice ("Unwrapping unit, found " ++ showVariant x)

unwrapInt :: Val -> Int
unwrapInt =
    \case
        VConst (Int n) -> n
        x -> ice ("Unwrapping int, found " ++ showVariant x)

unwrapBool :: Val -> Bool
unwrapBool =
    \case
        VConst (Bool b) -> b
        x -> ice ("Unwrapping bool, found " ++ showVariant x)

unwrapFun :: Val -> (Val -> IO Val)
unwrapFun =
    \case
        VFun f -> f
        x -> ice ("Unwrapping function, found " ++ showVariant x)

showVariant :: Val -> String
showVariant =
    \case
        VConst c ->
            case c of
                Unit -> "unit"
                Int _ -> "int"
                Double _ -> "double"
                Str _ -> "string"
                Bool _ -> "bool"
                Char _ -> "character"
        VFun _ -> "function"

ice :: String -> a
ice msg = error ("Internal compiler error: " ++ msg)
