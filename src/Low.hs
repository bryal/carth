module Low (module Low, Type(..)) where

import Monomorphic (Type(..))

type Block = ([Stmt], Terminator)

data Stmt
    = Do Instr
    | Let Name Instr

data Instr
    = Add Operand Operand
    | Mul Operand Operand

data Terminator
    = Ret Operand
    | Br Operand Label Label
    | Jmp Label

data Const
    = Int Int
    | F64 Double
    | Str Word

data Operand
    = Const Const
    | Local Type Name

type Name = String
type Label = String
