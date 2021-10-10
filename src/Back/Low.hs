{-# LANGUAGE TemplateHaskell #-}

module Back.Low (module Back.Low) where

import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Int

data Param name = ByVal name Type | ByRef name Type
data Ret = RetVal Type | RetVoid | OutParam Type

-- | There is no unit or void type. Instead, Lower has purged datatypes of ZSTs, and
--   void-returns and void-calls are their own variants. This isn't very elegant from a
--   functional perspective, but this fits imperative low-level IRs much better. In
--   particular, LLVM is kind of bad at handling {} as a ZST, and fails to optimize tail
--   calls returning {} in my experience.
data Type
    = TI8
    | TI16
    | TI32
    | TI64
    | TF32
    | TF64
    | TPtr Type
    | TFun [Param ()] Ret
    | TConst Word

data Const
    = Undef Type
    | I8 Int8
    | I16 Int16
    | I32 Int32
    | I64 Int
    | F32 Float
    | F64 Double
    | EnumVal GlobalId Word
    | Array Type [Const]
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
    | TBranch (Branch Terminator)

data LoopTerminator
    = Continue
    | Break
    | LBranch (Branch LoopTerminator)

data Expr
    = Add Operand Operand
    | Load Operand
    | Call Operand [Operand]
    | VoidCall Operand [Operand]
    | EBranch (Branch Expr)

data Block term = Block [Statement] term

type TypeNames = Vector String
type VarNames = Vector String

data FunDef = FunDef GlobalId [Param LocalId] Ret (Block Terminator) VarNames
data ExternDecl = ExternDecl String [Param ()] Ret
data GlobDef
    = GVarDef Global (Block Expr) VarNames
    | GConstDef Global Const

data Data = Data
    { dataName :: String
    , dataVariants :: Vector (String, [Type])
    , dataAlignment :: Word
    , dataSize :: Word
    }

data TypeDef
    = Enum String (Vector String)
    | Struct String [Type]
    | Data' Data

type TypeDefs = Vector TypeDef

data Program = Program [FunDef] [ExternDecl] [GlobDef] TypeDefs VarNames

typeName :: TypeDefs -> Word -> String
typeName ds i = typeName' (ds Vec.! fromIntegral i)

typeName' :: TypeDef -> String
typeName' = \case
    Enum n _ -> n
    Struct n _ -> n
    Data' (Data n _ _ _) -> n

