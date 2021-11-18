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
    | VoidPtr
    -- Really a function pointer, like `fn` in rust
    | TFun [Param ()] Ret
    | TConst Word

data LowInt
    = I8 Int8
    | I16 Int16
    | I32 Int32
    | I64 Prelude.Int

data Const
    = Undef Type
    | CInt LowInt
    | F32 Float
    | F64 Double
    | EnumVal GlobalId LowInt
    | Array Type [Const]
    | Zero Type

type LocalId = Word
type GlobalId = Word

data Local = Local LocalId Type
data Global = Global GlobalId Type

data Operand = OLocal Local | OGlobal Global | OConst Const

data Branch term
    = If Local (Block term) (Block term)
    | Switch Local [(Const, Block term)] (Block term)

data Statement
    = Let Local Expr
    | Store Operand Operand
    | SBranch (Branch ())
    | VoidCall Operand [Operand]
    | Do Expr

data Terminator
    = TRetVal Operand
    | TRetVoid
    | TOutParam Operand
    | TBranch (Branch Terminator)

data LoopTerminator
    = Continue [Operand]
    | Break Operand
    | LBranch (Branch LoopTerminator)

data Expr
    = Add Operand Operand
    | Sub Operand Operand
    | Mul Operand Operand
    | Load Operand
    | Call Operand [Operand]
    | Loop [(Local, Operand)] -- loop params
           Type -- loop return
           (Block LoopTerminator)
    | EBranch (Branch Expr)

data Block term = Block [Statement] term

type VarNames = Vector String

type Allocs = [(LocalId, Type)]

data FunDef = FunDef GlobalId [Param LocalId] Ret (Block Terminator) Allocs VarNames
data ExternDecl = ExternDecl String [Param ()] Ret
data GlobDef
    = GVarDef Global (Block Expr) VarNames
    | GConstDef Global Const

data Struct = Struct
    { structName :: String
    , structMembers :: [Type]
    , structAlignment :: Word
    , structSize :: Word
    }

data Data = Data
    { dataName :: String
    , dataVariants :: Vector (String, [Type])
    -- Alignment of the complete representing type
    , dataAlignment :: Word
    , dataSize :: Word
    -- Max alignment of all variants, excluding tag
    , dataAlignmentMax :: Word
    }

data TypeDef
    = DEnum String (Vector String)
    | DStruct Struct
    | DData Data

type TypeDefs = Vector TypeDef

data Program = Program [FunDef] [ExternDecl] [GlobDef] TypeDefs VarNames

typeName :: TypeDefs -> Word -> String
typeName ds i = typeName' (ds Vec.! fromIntegral i)

typeName' :: TypeDef -> String
typeName' = \case
    DEnum n _ -> n
    DStruct s -> structName s
    DData d -> dataName d

setTypeName :: String -> TypeDef -> TypeDef
setTypeName n = \case
    DEnum _ vs -> DEnum n vs
    DStruct s -> DStruct $ s { structName = n }
    DData d -> DData $ d { dataName = n }
