{-# LANGUAGE TemplateHaskell #-}

module Back.Low (module Back.Low) where

import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Int

import Sizeof hiding (sizeof)

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
    | EnumVal TypeId LowInt
    | Array Type [Const]
    | Zero Type

type LocalId = Word
type GlobalId = Word
type TypeId = Word

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
    | TOutParam Operand -- FIXME: This isn't right, right? If the last thing in the
                        -- function is a call for example, we want to pass along the sret
                        -- param, instead of allocating an extra stack variable to store
                        -- the call output in, before writing it to our own output param.
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
    { structMembers :: [Type]
    , structAlignment :: Word
    , structSize :: Word
    }

data Data = Data
    { dataVariants :: Vector (String, [Type])
    , dataGreatestSize :: Word
    , dataGreatestAlignment :: Word
    }

data TypeDef'
    = DEnum (Vector String)
    | DStruct Struct
    | DData Data

type TypeDef = (String, TypeDef')

type TypeDefs = Vector TypeDef

data Program = Program [FunDef] [ExternDecl] [GlobDef] TypeDefs VarNames

typeName :: TypeDefs -> Word -> String
typeName ds i = fst (ds Vec.! fromIntegral i)

sizeof :: Vector TypeDef -> Type -> Word
sizeof tenv = \case
    TI8 -> 1
    TI16 -> 2
    TI32 -> 4
    TI64 -> 8
    TF32 -> 4
    TF64 -> 8
    TPtr _ -> wordsize
    VoidPtr -> wordsize
    TFun _ _ -> wordsize
    TConst ix -> case snd (tenv Vec.! fromIntegral ix) of
        DEnum vs -> variantsTagBytes vs
        DStruct s -> structSize s
        DData (Data { dataVariants = vs, dataGreatestSize = s, dataGreatestAlignment = a })
            -> max (variantsTagBytes vs) a + a * div (s + a - 1) a

sizeofStruct :: Vector TypeDef -> [Type] -> Word
sizeofStruct tenv = foldl addMember 0
  where
    addMember accSize u =
        let align = alignmentof tenv u
            padding = if align == 0 then 0 else mod (align - accSize) align
            size = sizeof tenv u
        in  accSize + padding + size

alignmentof :: Vector TypeDef -> Type -> Word
alignmentof tenv = \case
    TConst ix -> case snd (tenv Vec.! fromIntegral ix) of
        DEnum vs -> variantsTagBytes vs
        DStruct s -> structAlignment s
        DData d -> max (variantsTagBytes (dataVariants d)) (dataGreatestAlignment d)
    t -> sizeof tenv t

alignmentofStruct :: Vector TypeDef -> [Type] -> Word
alignmentofStruct tenv = maximum . map (alignmentof tenv)
