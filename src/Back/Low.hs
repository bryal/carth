module Back.Low (module Back.Low, Access') where

import Data.Maybe
import Data.Vector (Vector)
import Numeric.Natural
import qualified Data.Vector as Vec

import Sizeof hiding (sizeof)
import Front.Monomorphic (Access', VariantIx)

data Param name = ByVal name Type | ByRef name Type deriving (Eq, Ord, Show)

mapParamName :: (nameA -> nameB) -> Param nameA -> Param nameB
mapParamName f = \case
    ByVal x t -> ByVal (f x) t
    ByRef x t -> ByRef (f x) t

dropParamName :: Param name -> Param ()
dropParamName = mapParamName (const ())

addParamName :: name -> Param () -> Param name
addParamName x = mapParamName (const x)

paramName :: Param name -> name
paramName = \case
    ByVal x _ -> x
    ByRef x _ -> x

paramType :: Param _name -> Type
paramType = \case
    ByVal _ t -> t
    ByRef _ t -> t

data Ret = RetVal Type | RetVoid deriving (Eq, Ord, Show)

-- | There is no unit or void type. Instead, Lower has purged datatypes of ZSTs, and
--   void-returns and void-calls are their own variants. This isn't very elegant from a
--   functional perspective, but this fits imperative low-level IRs much better. In
--   particular, LLVM is kind of bad at handling {} as a ZST, and fails to optimize tail
--   calls returning {} in my experience.
data Type
    = TInt { tintWidth :: Word } -- Signed integer
    | TNat { tnatWidth :: Word }
    | TF32
    | TF64
    | TPtr Type
    | VoidPtr
    -- Really a function pointer, like `fn` in rust
    | TFun [Param ()] Ret
    | TConst TypeId
    | TArray Type Word
    -- Closures are represented as a builtin struct named "closure", with a generic
    -- pointer to captures and a void-pointer representing the function. During lowering,
    -- we still need to remember the "real" type of the function.
    | TClosure [Param ()] Ret
  deriving (Eq, Ord, Show)

type Access = Access' Type

data Const
    = Undef Type
    | CInt { intWidth :: Word, intVal :: Integer }
    | CNat { natWidth :: Word, natVal :: Natural }
    | F32 Float
    | F64 Double
    | EnumVal { enumType :: TypeId, enumVariant :: String, enumWidth :: Word, enumVal :: Natural}
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
data Extern = Extern String [Param ()] Ret
    deriving (Show, Eq)

data Operand = OLocal Local | OGlobal Global | OConst Const | OExtern Extern deriving Show

data Branch a
    = BIf Operand (Block a) (Block a)
    | BSwitch Operand [(Const, Block a)] (Block a)
    deriving Show

data Statement
    = Let Local Expr
    | Store Operand Operand -- value -> destination
    | VoidCall Operand [Operand]
    | SLoop (Loop ())
    | SBranch (Branch ())
    deriving Show

data Terminator
    = TRetVal Expr
    | TRetVoid
    | TBranch (Branch Terminator)
    deriving Show

data LoopTerminator a
    = Continue [Operand]
    | Break a
    | LBranch (Branch (LoopTerminator a))
    deriving Show

data Loop a = Loop [(Local, Operand)] (Block (LoopTerminator a))
    deriving Show

data Expr'
    -- I know this doesn't map well to LLVM, but it makes codegen simpler, and it works
    -- with C anyhow. Will just have to work around it a little in LLVM.
    = EOperand Operand
    | Add Operand Operand
    | Sub Operand Operand
    | Mul Operand Operand
    | Div Operand Operand
    | Rem Operand Operand
    | Shl Operand Operand
    | LShr Operand Operand
    | AShr Operand Operand
    | BAnd Operand Operand
    | BOr Operand Operand
    | BXor Operand Operand
    | Eq Operand Operand
    | Ne Operand Operand
    | Gt Operand Operand
    | GtEq Operand Operand
    | Lt Operand Operand
    | LtEq Operand Operand
    | Load Operand
    | Call Operand [Operand]
    | ELoop (Loop Expr)
    -- Given a pointer to a struct, get a pointer to the Nth member of that struct
    | EGetMember Word Operand
    -- Given a pointer to an untagged union, get it as a specific variant
    | EAsVariant Operand VariantIx
    | EBranch (Branch Expr)
    | Cast Operand Type -- C-style cast
    | Bitcast Operand Type
    deriving Show

data Expr = Expr
    { eInner :: Expr'
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

data FunDef = FunDef
    { funDefName :: GlobalId
    , funDefParams :: [Param LocalId]
    , funDefRet :: Ret
    , funDefBody :: Block Terminator
    , funDefAllocs :: Allocs
    , funDefLocalNames :: VarNames
    }
    deriving Show
data ExternDecl = ExternDecl String [Param ()] Ret
    deriving Show

type GlobVarDecl = Global
newtype GlobDef = GlobVarDecl GlobVarDecl
    deriving Show

data Struct = Struct
    -- TODO: Members should include names. Needed in C, and possibly other backends.
    { structMembers :: [Type]
    , structAlignment :: Word
    , structSize :: Word
    }
    deriving (Show, Eq, Ord)

data Union = Union
    { unionVariants :: Vector (String, TypeId)
    , unionGreatestSize :: Word
    , unionGreatestAlignment :: Word
    }
    deriving (Show, Eq, Ord)

data TypeDef'
    = DEnum (Vector String)
    | DStruct Struct
    | DUnion Union
    deriving (Show, Eq, Ord)

type TypeDef = (String, TypeDef')

type TypeDefs = Vector TypeDef

data Program = Program [FunDef] [ExternDecl] [GlobDef] TypeDefs VarNames
    deriving Show

typeName :: TypeDefs -> Word -> String
typeName ds i = fst (ds Vec.! fromIntegral i)

integralWidth :: Type -> Maybe Word
integralWidth = \case
    TInt w -> Just w
    TNat w -> Just w
    _ -> Nothing

isIntegral :: Type -> Bool
isIntegral t = isInt t || isNat t

isInt :: Type -> Bool
isInt = \case
    TInt _ -> True
    _ -> False

isNat :: Type -> Bool
isNat = \case
    TNat _ -> True
    _ -> False

isFloat :: Type -> Bool
isFloat = \case
    TF32 -> True
    TF64 -> True
    _ -> False

sizeof :: (TypeId -> Maybe TypeDef) -> Type -> Word
sizeof tenv = \case
    TInt { tintWidth = w } -> div w 8
    TNat { tnatWidth = w } -> div w 8
    TF32 -> 4
    TF64 -> 8
    TPtr _ -> wordsize
    VoidPtr -> wordsize
    TFun _ _ -> wordsize
    TClosure _ _ -> 2 * wordsize
    TConst ix -> case fmap snd (tenv ix) of
        Nothing -> 0
        Just (DEnum vs) -> variantsTagBytes vs
        Just (DStruct s) -> structSize s
        Just (DUnion Union { unionGreatestSize = s, unionGreatestAlignment = a }) ->
            a * div (s + a - 1) a
    TArray t n -> sizeof tenv t * n

sizeofStruct :: (TypeId -> Maybe TypeDef) -> [Type] -> Word
sizeofStruct tenv = foldl addMember 0
  where
    addMember accSize u =
        let align = alignmentof tenv u
            padding = if align == 0 then 0 else mod (align - accSize) align
            size = sizeof tenv u
        in  accSize + padding + size

alignmentof :: (TypeId -> Maybe TypeDef) -> Type -> Word
alignmentof tenv = \case
    TConst ix -> case snd (fromJust (tenv ix)) of
        DEnum vs -> variantsTagBytes vs
        DStruct s -> structAlignment s
        DUnion u -> unionGreatestAlignment u
    t -> sizeof tenv t

alignmentofStruct :: (TypeId -> Maybe TypeDef) -> [Type] -> Word
alignmentofStruct tenv = maximum . map (alignmentof tenv)

mkEOperand :: Operand -> Expr
mkEOperand op = Expr (EOperand op) (typeof op)

class TypeOf a where
    typeof :: a -> Type

instance TypeOf Operand where
    typeof = \case
        OLocal l -> typeof l
        OGlobal g -> typeof g
        OConst c -> typeof c
        OExtern e -> typeof e

instance TypeOf Expr where
    typeof (Expr _ t) = t

instance TypeOf Local where
    typeof (Local _ t) = t

instance TypeOf Global where
    typeof (Global _ t) = t

instance TypeOf Extern where
    typeof (Extern _ ps r) = TFun ps r

instance TypeOf Const where
    typeof = \case
        Undef t -> t
        CInt { intWidth = w } -> TInt { tintWidth = w }
        CNat { natWidth = w } -> TNat { tnatWidth = w }
        F32 _ -> TF32
        F64 _ -> TF64
        EnumVal { enumType = tid } -> TConst tid
        Array t cs -> TArray t (fromIntegral (length cs))
        Zero t -> t

instance (TypeOf a, TypeOf b) => TypeOf (Either a b) where
    typeof = either typeof typeof

instance Semigroup a => Semigroup (Block a) where
    (<>) (Block stms1 a) (Block stms2 b) = Block (stms1 ++ stms2) (a <> b)

instance Monoid a => Monoid (Block a) where
    mempty = Block [] mempty
