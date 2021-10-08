{-# LANGUAGE TemplateHaskell #-}

module Back.Low (module Back.Low) where

import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Int

type Type = Word


data Const
    = Undef Type
    | I8 Int8
    | I16 Int16
    | I32 Int32
    | I64 Int
    | F32 Float
    | F64 Double
    | Array [Type]
    | Zero Type

type LocalId = Word
type GlobalId = Word

data Local = Local LocalId Type
data Global = Global GlobalId Type

data Operand = OLocal Local | OGlobal Global | OConst Const


data Branch term
    = If Local (Block term) (Block term)
    | Switch Operand [(Const, Block term)] (Block term)

data Statement
    = Let Local Expr
    | Store Operand Operand
    | Loop (Block LoopTerminator)
    | SBranch (Branch ())
    | Do Expr

data Terminator
    = Ret Operand
    | TBranch Terminator

data LoopTerminator
    = Continue
    | Break
    | LBranch (Branch LoopTerminator)

data Expr
    = Add Operand Operand
    | Load Operand
    | Call Operand [Operand]
    | EBranch (Branch Expr)

data Block term = Block [Statement] term

type TypeNames = Vector String
type VarNames = Vector String

data FunDef = FunDef GlobalId [(LocalId, Type)] Type (Block Terminator) VarNames
data ExternDecl = ExternDecl GlobalId [Type] Type
data GlobDef
    = GVarDef Global Const
    | GConstDef Global Const

data Data = Data
    { dataName :: String
    , dataVariants :: Vector (String, [Type])
    , dataAlignment :: Word
    , dataSize :: Word
    }

data TypeDef
    = Unit String
    | Enum String (Vector String)
    | Struct String [Type]
    | Data' Data

type TypeDefs = Vector TypeDef

data Program = Program [FunDef] [ExternDecl] [GlobDef] TypeDefs VarNames

typeName :: TypeDefs -> Word -> String
typeName ds i = typeName' (ds Vec.! fromIntegral i)

typeName' :: TypeDef -> String
typeName' = \case
    Unit n -> n
    Enum n _ -> n
    Struct n _ -> n
    Data' (Data n _ _ _) -> n

