module Back.Low (module Back.Low) where

import Data.Bifunctor
import Data.Char
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Vector (Vector)
import Data.Word
import Numeric.Natural
import qualified Data.Vector as Vec
import Text.Printf

import Misc
import Sizeof hiding (sizeof, alignmentof)
import Pretty
import Front.Monomorphic (VariantIx)

data Sized x = ZeroSized | Sized x deriving (Show, Ord, Eq)

mapSized :: (a -> b) -> Sized a -> Sized b
mapSized f (Sized a) = Sized (f a)
mapSized _ ZeroSized = ZeroSized

mapSizedM :: Monad m => (a -> m b) -> Sized a -> m (Sized b)
mapSizedM f = \case
    Sized a -> fmap Sized (f a)
    ZeroSized -> pure ZeroSized

sized :: b -> (a -> b) -> Sized a -> b
sized b f = \case
    ZeroSized -> b
    Sized a -> f a

sizedMaybe :: Sized a -> Maybe a
sizedMaybe = \case
    ZeroSized -> Nothing
    Sized t -> Just t

fromSized :: Sized a -> a
fromSized = \case
    ZeroSized -> ice "Lower.fromSized: was ZeroSized"
    Sized x -> x

catSized :: [Sized a] -> [a]
catSized = mapMaybe sizedMaybe

data Pass a
    = InReg a
    | OnStack a
    deriving (Eq, Ord, Show)

passed :: Pass a -> a
passed = \case
    InReg a -> a
    OnStack a -> a

passLike :: Pass _a -> b -> Pass b
passLike = \case
    InReg _ -> InReg
    OnStack _ -> OnStack

data OutParam name = OutParam
    { outParamName :: name
    , outParamType :: Type
    }
    deriving (Eq, Ord, Show)

outParamLocal :: OutParam LocalId -> Local
outParamLocal (OutParam x t) = Local x (TPtr t)

data Ret = RetVal Type | RetVoid deriving (Eq, Ord, Show)

-- | There is no unit or void type. Instead, Lower has purged datatypes of ZSTs, and void-returns
--   and void-calls are their own variants. This isn't very elegant from a functional perspective,
--   but this fits imperative low-level IRs much better. In particular, LLVM is kind of bad at
--   handling {} as a ZST, and fails to optimize tail calls returning {} in my experience.
data Type
    = TInt { tintWidth :: Word } -- Signed integer
    | TNat { tnatWidth :: Word }
    | TF32
    | TF64
    | TPtr Type
    | VoidPtr
    -- Really a function pointer, like `fn` in rust
    | TFun (Maybe (OutParam ())) [Pass Type] Ret
    | TConst TypeId
    | TArray Type Word
    -- Closures are represented as a builtin struct named "closure", with a generic pointer to
    -- captures and a void-pointer representing the function. During lowering, we still need to
    -- remember the "real" type of the function.
    | TClosure (Maybe (OutParam ())) [Pass Type] Ret
  deriving (Eq, Ord, Show)

type MemberIx = Word

data Const
    = Undef Type
    | CInt { intWidth :: Word, intVal :: Integer }
    | CNat { natWidth :: Word, natVal :: Natural }
    | F32 Float
    | F64 Double
    | EnumVal { enumType :: TypeId, enumVariant :: GlobalId, enumWidth :: Word, enumVal :: Natural}
    | Array Type [Const]
    | CharArray [Word8]
    | Zero Type
    | CBitcast Const Type
    | CGlobal Global
    | CStruct Type [Const]
    | CPtrIndex Const Word
    deriving Show

type LocalId = Word
newtype GlobalId = GID Word deriving (Show, Ord, Eq)
type TypeId = Word

unGid :: GlobalId -> Word
unGid (GID gid) = gid

data Local = Local LocalId Type
    deriving Show
data Global = Global GlobalId Type -- Type including the pointer
    deriving (Show, Eq)
data Extern = Extern String (Maybe (OutParam ())) [Pass Type] Ret
    deriving (Show, Eq)

data Operand
    = OLocal Local
    | OGlobal Global
    | OConst Const
    | OExtern Extern
    deriving Show

data Branch a
    = BIf Operand (Block a) (Block a)
    | BSwitch Operand [(Const, Block a)] (Block a)
    deriving Show

data Statement
    = Let Local Expr
    | Store Operand Operand -- value -> destination
    | VoidCall Operand (Maybe Operand) [Pass Operand]
    | SLoop (Loop ())
    | SBranch (Branch ())
    deriving Show

data Terminator
    = TRetVal Expr
    | TRetVoid
    deriving Show

data LoopTerminator a
    = Continue [Operand]
    | Break a
    | LBranch (Branch (LoopTerminator a))
    deriving Show

data Loop a = Loop [(Local, Operand)] (Block (LoopTerminator a))
    deriving Show

data Expr'
    -- I know this doesn't map well to LLVM, but it makes codegen simpler, and it works with C
    -- anyhow. Will just have to work around it a little in LLVM.
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
    | Call Operand [Pass Operand]
    | ELoop (Loop Expr)
    -- Given a pointer to a struct, get a pointer to the Nth member of that struct
    | EGetMember MemberName Operand
    -- Given a pointer to an untagged union, get it as a specific variant
    | EAsVariant Operand VariantIx
    | EBranch (Branch Expr)
    | Cast Operand Type -- ^ C-style cast
    -- | Bitwise cast of {int,pointer}-to-{int,pointer}. Structs are by nature bitwisely cast by
    --   putting them on the stack and casting the pointer. Floats are cast to and from other types
    --   via the stack as well, just to make codegen of C simpler.
    | Bitcast Operand Type
    -- | In the body of a function, given one of its parameters that was passed on the stack, get a
    --   pointer to the structure. Different backends diverge in how they represent stack-passing,
    --   and this is how we converge.
    | OnStackAsIndirect LocalId Type
    | OnStackAsDirect LocalId Type
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

type FunDefParams = [(LocalId, Pass Type)]

data FunDef = FunDef
    { funDefName :: GlobalId
    , funDefOutParam :: Maybe (OutParam LocalId)
    , funDefParams :: FunDefParams
    , funDefRet :: Ret
    , funDefBody :: Block Terminator
    , funDefAllocs :: Allocs
    , funDefLocalNames :: VarNames
    }
    deriving Show
data ExternDecl = ExternDecl String (Maybe (OutParam ())) [Pass Type] Ret
    deriving Show

data GlobDef
    = GlobVarDecl GlobalId Type
    | GlobConstDef GlobalId Type Const
    deriving Show

data MemberName
    = MemberId Word
    | MemberName String
    deriving (Show, Eq, Ord)

data Struct = Struct
    { structMembers :: [(MemberName, Type)]
    , structSize :: Word
    , structAlignment :: Word
    }
    deriving (Show, Eq, Ord)

lookupMember :: MemberName -> Struct -> Maybe Type
lookupMember m = lookup m . structMembers

data Union = Union
    { unionVariants :: Vector (String, Sized TypeId)
    , unionGreatestSize :: Word
    , unionGreatestAlignment :: Word
    }
    deriving (Show, Eq, Ord)

data TypeDef'
    = DEnum (Vector GlobalId)
    | DStruct Struct
    | DUnion Union
    deriving (Show, Eq, Ord)

type TypeDef = (String, TypeDef')

type MainRef = Global
type InitRef = Global

-- The `TypeDef`s are not yet resolved for name conflicts. You should apply
-- `Lower.resolveTypeNameConflicts` after replacing any backend-specific invalid ident chars.
data Program = Program [FunDef] [ExternDecl] [GlobDef] [TypeDef] VarNames MainRef InitRef
    deriving Show

typeName :: Vector TypeDef -> Word -> String
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

isPtr :: Type -> Bool
isPtr = \case
    TPtr _ -> True
    _ -> False

pointee :: Type -> Type
pointee = \case
    TPtr t -> t
    t -> ice $ "Low.pointee of non pointer type " ++ show t

asTConst :: Type -> TypeId
asTConst (TConst tid) = tid
asTConst t = ice $ "Low.asTConst of non TConst type " ++ show t

sizeof :: (TypeId -> TypeDef) -> Type -> Word
sizeof tenv = \case
    TInt { tintWidth = w } -> div w 8
    TNat { tnatWidth = w } -> div w 8
    TF32 -> 4
    TF64 -> 8
    TPtr _ -> wordsize
    VoidPtr -> wordsize
    TFun{} -> wordsize
    TClosure{} -> 2 * wordsize
    TConst ix -> case snd (tenv ix) of
        DEnum vs -> variantsTagBytes vs
        DStruct s -> structSize s
        DUnion Union { unionGreatestSize = s, unionGreatestAlignment = a } ->
            a * div (s + a - 1) a
    TArray t n -> sizeof tenv t * n

sizeofStruct :: (TypeId -> TypeDef) -> [Type] -> Word
sizeofStruct tenv = foldl addMember 0
  where
    addMember accSize u =
        let align = alignmentof tenv u
            padding = if align == 0 then 0 else mod (align - accSize) align
            size = sizeof tenv u
        in  accSize + padding + size

alignmentof :: (TypeId -> TypeDef) -> Type -> Word
alignmentof tenv = \case
    TConst ix -> case snd (tenv ix) of
        DEnum vs -> variantsTagBytes vs
        DStruct s -> structAlignment s
        DUnion u -> unionGreatestAlignment u
    t -> sizeof tenv t

alignmentofStruct :: (TypeId -> TypeDef) -> [Type] -> Word
alignmentofStruct tenv = maximum . map (alignmentof tenv)

mkEOperand :: Operand -> Expr
mkEOperand op = Expr (EOperand op) (typeof op)

decodeCharArrayStrLit :: (Word8 -> String) -> [Word8] -> String
decodeCharArrayStrLit escapeInvisible cs = do
    c <- cs
    if
        | c == 0x22 -> "\\\""
        | c == 0x5C -> "\\\\"
        | 0x20 <= c && c <= 0x7E -> [chr (fromIntegral c)]
        | otherwise -> escapeInvisible c

resolveTypeNameConflicts :: [String] -> [TypeDef] -> [TypeDef]
resolveTypeNameConflicts alreadyDefined =
    uncurry zip . first (resolveNameConflicts alreadyDefined) . unzip

resolveNameConflicts :: [String] -> [String] -> [String]
resolveNameConflicts fixedNames names = reverse . snd $ foldl'
    (\(seen, acc) name ->
        let n = fromMaybe (0 :: Word) (Map.lookup name seen)
            (n', name') = incrementUntilUnseen seen n name
        in  (Map.insert name' 1 (Map.insert name (n' + 1) seen), name' : acc)
    )
    (Map.fromList (zip fixedNames (repeat 1)), [])
    names
  where
    incrementUntilUnseen seen n name =
        let name' = if n == 0 then name else name ++ "_" ++ show n
        in  if Map.member name' seen then incrementUntilUnseen seen (n + 1) name else (n, name')

builtinType :: String -> Type
builtinType name = TConst . fromIntegral . fromJust $ findIndex ((== name) . fst) builtinTypeDefs

builtinTypeDefs :: [TypeDef]
builtinTypeDefs =
    -- closure: pointer to captures struct & function pointer, genericized
    [ ( "closure"
      , DStruct Struct
          { structMembers = [(MemberName "captures", VoidPtr), (MemberName "function", VoidPtr)]
          , structSize = wordsize * 2
          , structAlignment = wordsize
          }
      )
    ]

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
    typeof (Extern _ out ps r) = TFun out ps r

instance TypeOf Const where
    typeof = \case
        Undef t -> t
        CInt { intWidth = w } -> TInt { tintWidth = w }
        CNat { natWidth = w } -> TNat { tnatWidth = w }
        F32 _ -> TF32
        F64 _ -> TF64
        EnumVal { enumType = tid } -> TConst tid
        Array t cs -> TArray t (fromIntegral (length cs))
        CharArray cs -> TArray (TNat 8) (fromIntegral (length cs))
        CStruct t _ -> t
        CBitcast _ t -> t
        CGlobal (Global _ t) -> t
        Zero t -> t
        CPtrIndex p _ -> typeof p

instance (TypeOf a, TypeOf b) => TypeOf (Either a b) where
    typeof = either typeof typeof

instance Semigroup a => Semigroup (Block a) where
    (<>) (Block stms1 a) (Block stms2 b) = Block (stms1 ++ stms2) (a <> b)

instance Monoid a => Monoid (Block a) where
    mempty = Block [] mempty

instance Pretty Program where
    pretty' _ = prettyProgram

prettyProgram :: Program -> String
prettyProgram (Program fdefs edecls gdefs tdefs gnames main init) =
    intercalate "\n\n" (map (uncurry pTdef) (Vec.toList tdefs'))
        ++ "\n\n"
        ++ intercalate "\n" (map pEdecl edecls)
        ++ "\n\n"
        ++ intercalate "\n" (map pGdef gdefs)
        ++ "\n\n"
        ++ intercalate "\n\n" (map pFdef fdefs)
        ++ ("\n\n; Main: " ++ pGlobal main)
        ++ ("\n\n; Init: " ++ pGlobal init)
  where
    tdefs' = Vec.fromList (resolveTypeNameConflicts [] tdefs)
    pTdef name = \case
        DEnum vs ->
            ("enum " ++ name ++ " {")
                ++ concatMap (\x -> "\n    " ++ gname x ++ ",") (Vec.toList vs)
                ++ "\n}"
        DStruct (Struct ms s a) ->
            ("struct " ++ name ++ " {")
                ++ concatMap pMember ms
                ++ ("\n} // size: " ++ show s ++ ", alignment: " ++ show a)
        DUnion (Union vs gs ga) ->
            ("union " ++ name ++ " {")
                ++ concatMap
                       (\(x, ti) -> "\n    " ++ x ++ ": " ++ sized "void" typeName ti ++ ",")
                       (Vec.toList vs)
                ++ ("\n} // greatest size: " ++ show gs)
                ++ (", greatest alignment: " ++ show ga)
    pMember (x, t) =
        let sx = case x of
                MemberId i -> show i
                MemberName s -> s
        in  "\n    " ++ sx ++ ": " ++ pType t ++ ","
    pType = \case
        TInt width -> "i" ++ show width
        TNat width -> "n" ++ show width
        TF32 -> "f32"
        TF64 -> "f64"
        TPtr t -> "*" ++ pType t
        VoidPtr -> "*void"
        TFun outParam params ret ->
            "fun("
                ++ intercalate
                       ", "
                       (maybe id ((:) . pAnonOutParam) outParam $ map pAnonParam params)
                ++ ") -> "
                ++ pRet ret
        TConst ti -> typeName ti
        TArray t n -> "[" ++ pType t ++ "; " ++ show n ++ "]"
        TClosure outParam params ret ->
            "clo("
                ++ intercalate
                       ", "
                       (maybe id ((:) . pAnonOutParam) outParam $ map pAnonParam params)
                ++ ") -> "
                ++ pRet ret
    typeName ti = fst $ tdefs' Vec.! fromIntegral ti
    pEdecl (ExternDecl name outParam params ret) =
        ("extern @" ++ name ++ "(")
            ++ intercalate ", " (maybe id ((:) . pAnonOutParam) outParam $ map pAnonParam params)
            ++ (") -> " ++ pRet ret ++ ";")
    pAnonOutParam (OutParam _ t) = "out " ++ pType (TPtr t)
    pAnonParam = \case
        InReg t -> pType t
        OnStack t -> "onstack " ++ pType t
    pRet = \case
        RetVal t -> pType t
        RetVoid -> "void"
    pFdef (FunDef name out params ret body allocs lnames) =
        ("fun @" ++ gname name ++ "(")
            ++ intercalate ", " (maybe id ((:) . pOutParam) out $ map pParam params)
            ++ (") -> " ++ pRet ret ++ " {")
            ++ precalate "\n    " (map pAlloc allocs)
            ++ (if null allocs then "" else "\n    ")
            ++ pBlock' 4 pTerm body
            ++ "\n}"
      where
        pOutParam (OutParam x t) = "out " ++ lname x ++ ": " ++ pType t
        pParam (x, pass) = case pass of
            InReg t -> lname x ++ ": " ++ pType t
            OnStack t -> "onstack " ++ lname x ++ ": " ++ pType t
        pAlloc (lid, t) = "var %" ++ lname lid ++ ": " ++ pType t ++ ";"
        pBlock :: Int -> (Int -> term -> String) -> Block term -> String
        pBlock d pTerm' blk = "{" ++ pBlock' (d + 4) pTerm' blk ++ ("\n" ++ indent d ++ "}")
        pBlock' :: Int -> (Int -> term -> String) -> Block term -> String
        pBlock' d pTerm' (Block stms term) =
            precalate ("\n" ++ indent d) (map (pStm d) stms) ++ case pTerm' d term of
                "" -> ""
                s -> "\n" ++ indent d ++ s
        pTerm d = \case
            TRetVal e -> "return " ++ pExpr d e ++ ";"
            TRetVoid -> "return void;"
        pStm d = \case
            Let lhs e ->
                ("let " ++ pLocal lhs)
                    ++ (": " ++ pType (eType e))
                    ++ (" = " ++ pExpr (d + 4) e ++ ";")
            Store x dst -> "store " ++ pOp x ++ " -> " ++ pOp dst ++ ";"
            VoidCall f out as ->
                "call "
                    ++ pOp f
                    ++ "("
                    ++ intercalate ", " (maybe id ((:) . pOutArg) out $ map pArg as)
                    ++ ");"
            SLoop lp -> pLoop d (\_ () -> "") lp
            SBranch br -> pBranch d (\_ () -> "") br
        pArg = \case
            InReg x -> pOp x
            OnStack x -> "onstack " ++ pOp x
        pOutArg x = "out " ++ pOp x
        pBranch :: Int -> (Int -> term -> String) -> Branch term -> String
        pBranch d pTerm' = \case
            BIf p c a ->
                ("if " ++ pOp p) ++ (" " ++ pBlock d pTerm' c) ++ (" else " ++ pBlock d pTerm' a)
            BSwitch m cs def ->
                ("switch " ++ pOp m ++ " {")
                    ++ precalate ("\n" ++ indent d) (map (pCase d pTerm') cs)
                    ++ ("\n" ++ indent d ++ "default " ++ pBlock d pTerm' def)
        pCase :: Int -> (Int -> term -> String) -> (Const, Block term) -> String
        pCase d pTerm' (c, blk) = "case " ++ pConst c ++ " " ++ pBlock d pTerm' blk
        pLoop :: Int -> (Int -> a -> String) -> Loop a -> String
        pLoop d pTerm' (Loop args body) =
            ("loop (" ++ intercalate ", " (map pLoopArg args) ++ ") ")
                ++ pBlock d (pLoopTerm pTerm') body
        pLoopArg (lhs, rhs) = pLocal lhs ++ " = " ++ pOp rhs
        pLoopTerm :: (Int -> term -> String) -> Int -> LoopTerminator term -> String
        pLoopTerm pTerm' d = \case
            Continue vs -> "continue (" ++ intercalate ", " (map pOp vs) ++ ");"
            Break a -> "break " ++ pTerm' d a ++ ";"
            LBranch br -> pBranch d (pLoopTerm pTerm') br
        pExpr d (Expr e t) = case e of
            EOperand op -> pOp op
            Add a b -> pOp a ++ " + " ++ pOp b
            Sub a b -> pOp a ++ " - " ++ pOp b
            Mul a b -> pOp a ++ " * " ++ pOp b
            Div a b -> pOp a ++ " / " ++ pOp b
            Rem a b -> pOp a ++ " % " ++ pOp b
            Shl a b -> pOp a ++ " << " ++ pOp b
            LShr a b -> pOp a ++ " l>> " ++ pOp b
            AShr a b -> pOp a ++ " a>> " ++ pOp b
            BAnd a b -> pOp a ++ " & " ++ pOp b
            BOr a b -> pOp a ++ " | " ++ pOp b
            BXor a b -> pOp a ++ " x| " ++ pOp b
            Eq a b -> pOp a ++ " == " ++ pOp b
            Ne a b -> pOp a ++ " != " ++ pOp b
            Gt a b -> pOp a ++ " > " ++ pOp b
            GtEq a b -> pOp a ++ " >= " ++ pOp b
            Lt a b -> pOp a ++ " < " ++ pOp b
            LtEq a b -> pOp a ++ " <= " ++ pOp b
            Load addr -> "load " ++ pOp addr
            Call f as -> pOp f ++ "(" ++ intercalate ", " (map pArg as) ++ ")"
            ELoop loop -> pLoop d pExpr loop
            EGetMember i struct -> pOp struct ++ "->" ++ show i
            EAsVariant x _vi -> pOp x ++ " as " ++ pType t
            EBranch br -> pBranch d pExpr br
            Cast x t -> "cast " ++ pOp x ++ " to " ++ pType t
            Bitcast x t -> "bitcast " ++ pOp x ++ " to " ++ pType t
            OnStackAsDirect x t -> "onstack-as-direct " ++ pLocal (Local x (TPtr t))
            OnStackAsIndirect x t -> "onstack-as-indirect " ++ pLocal (Local x (TPtr t))
        pOp = \case
            OLocal l -> pLocal l
            OGlobal g -> pGlobal g
            OConst c -> pConst c
            OExtern (Extern x _ _ _) -> "@" ++ x
        pLocal (Local x _) = "%" ++ lname x
        lname lid = lnames Vec.! fromIntegral lid
    pGdef = \case
        GlobVarDecl x t -> "var @" ++ gname x ++ ": " ++ pType t ++ ";"
        GlobConstDef x t rhs ->
            "const @" ++ gname x ++ ": " ++ pType t ++ " = " ++ pConst rhs ++ ";"
    pConst = \case
        Undef _ -> "undefined"
        CInt { intVal = n } -> show n
        CNat { natVal = n } -> show n
        F32 x -> show x
        F64 x -> show x
        EnumVal { enumVariant = v } -> gname v
        Array _ xs -> "[" ++ intercalate ", " (map pConst xs) ++ "]"
        CharArray cs -> "\"" ++ decodeCharArrayStrLit (printf "\\x%02X") cs ++ "\""
        Zero _ -> "zero"
        CBitcast x t -> "(bitcast " ++ pConst x ++ " to " ++ pType t ++ ")"
        CGlobal g -> pGlobal g
        CStruct t ms -> "(" ++ pType t ++ "){ " ++ intercalate ", " (map pConst ms) ++ " }"
        CPtrIndex p i -> pConst p ++ "[" ++ show i ++ "]"
    pGlobal (Global x _) = "@" ++ gname x
    gname (GID gid) = gnames Vec.! fromIntegral gid
