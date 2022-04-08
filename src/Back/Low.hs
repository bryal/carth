module Back.Low (module Back.Low, Access') where

import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Int

import Sizeof hiding (sizeof)
import Front.Monomorphic (Access')

data Param name = ByVal name Type | ByRef name Type deriving (Eq, Ord, Show)
data Ret = RetVal Type | RetVoid deriving (Eq, Ord, Show)

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
    | TConst TypeId
    | TArray Type Word
  deriving (Eq, Ord, Show)

type Access = Access' Type

data LowInt
    = I8 Int8
    | I16 Int16
    | I32 Int32
    | I64 Prelude.Int
    deriving Show

data Const
    = Undef Type
    | CInt LowInt
    | F32 Float
    | F64 Double
    | EnumVal TypeId LowInt
    | Array Type [Const]
    | Zero Type
    deriving Show

type LocalId = Word
type GlobalId = Word
type TypeId = Word

data Local = Local LocalId Type
    deriving Show
data Global = Global GlobalId Type -- Type excluding the pointer
    deriving (Show, Eq)

data Operand = OLocal Local | OGlobal Global | OConst Const deriving Show

data Branch term
    = BIf Local (Block (Branch term)) (Block (Branch term))
    | BSwitch Local [(Const, Block (Branch term))] (Block (Branch term))
    | BLeaf term
    deriving Show

data Statement'
    = Let Local Expr
    | Store Operand Operand -- value -> destination
    | VoidCall Operand [Operand]
    -- | Do Expr
    | SLoop (Loop ())
    deriving Show

type Statement = Branch Statement'

data Terminator'
    = TRetVal Expr
    | TRetVoid
    deriving Show

type Terminator = Branch Terminator'

data LoopTerminator' a
    = Continue [Operand]
    | Break a
    deriving Show

type LoopTerminator a = Branch (LoopTerminator' a)

data Loop a = Loop [(Local, Operand)] (Block (LoopTerminator a))
    deriving Show

data Expr'
    -- I know this doesn't map well to LLVM, but it makes codegen simpler, and it works
    -- with C anyhow. Will just have to work around it a little in LLVM.
    = EOperand Operand
    | Add Operand Operand
    | Sub Operand Operand
    | Mul Operand Operand
    | Load Operand
    | Call Operand [Operand]
    | ELoop (Loop Expr)
    -- Given a pointer to a struct, get a pointer to the Nth member of that struct
    | EGetMember Word Operand
    -- Given a pointer to an untagged union, get it as a specific variant
    | EAsVariant Operand Word
    deriving Show

data Expr = Expr
    { eInner :: Branch Expr'
    , eType :: Type
    }
    deriving Show

data Block term = Block
    { blockStms :: [Statement]
    , blockTerm :: term
    }
    deriving Show

type VarNames = Vector String

type Allocs = [(LocalId, Type)]

data FunDef = FunDef GlobalId [Param LocalId] Ret (Block Terminator) Allocs VarNames
    deriving Show
data ExternDecl = ExternDecl String [Param ()] Ret
    deriving Show
data GlobDef
    = GVarDef Global (Block Expr) VarNames
    | GConstDef Global Const
    deriving Show

data Struct = Struct
    { structMembers :: [Type]
    , structAlignment :: Word
    , structSize :: Word
    }
    deriving Show

data Union = Union
    { unionVariants :: Vector (String, TypeId)
    , unionGreatestSize :: Word
    , unionGreatestAlignment :: Word
    }
    deriving Show

data TypeDef'
    = DEnum (Vector String)
    | DStruct Struct
    | DUnion Union
    deriving Show

type TypeDef = (String, TypeDef')

type TypeDefs = Vector TypeDef

data Program = Program [FunDef] [ExternDecl] [GlobDef] TypeDefs VarNames
    deriving Show

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
        DUnion Union { unionGreatestSize = s, unionGreatestAlignment = a } ->
            a * div (s + a - 1) a
    TArray t n -> sizeof tenv t * n

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
        DUnion u -> unionGreatestAlignment u
    t -> sizeof tenv t

alignmentofStruct :: Vector TypeDef -> [Type] -> Word
alignmentofStruct tenv = maximum . map (alignmentof tenv)

class TypeOf a where
    typeof :: a -> Type

instance TypeOf Operand where
    typeof = \case
        OLocal l -> typeof l
        OGlobal g -> typeof g
        OConst c -> typeof c

instance TypeOf Expr where
    typeof (Expr _ t) = t

instance TypeOf Local where
    typeof (Local _ t) = t

instance TypeOf Global where
    typeof (Global _ t) = TPtr t

instance TypeOf Const where
    typeof = \case
        Undef t -> t
        CInt i -> typeof i
        F32 _ -> TF32
        F64 _ -> TF64
        EnumVal tid _ -> TConst tid
        Array t cs -> TArray t (fromIntegral (length cs))
        Zero t -> t

instance TypeOf LowInt where
    typeof = \case
        I8 _ -> TI8
        I16 _ -> TI16
        I32 _ -> TI32
        I64 _ -> TI64

instance (TypeOf a, TypeOf b) => TypeOf (Either a b) where
    typeof = either typeof typeof

instance Semigroup a => Semigroup (Block a) where
    (<>) (Block stms1 a) (Block stms2 b) = Block (stms1 ++ stms2) (a <> b)

instance Monoid a => Monoid (Block a) where
    mempty = Block [] mempty
