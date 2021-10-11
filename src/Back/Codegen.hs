{-# LANGUAGE DuplicateRecordFields, GADTs, RankNTypes #-}

-- | Generation of LLVM IR code from our monomorphic AST.
module Back.Codegen (codegen) where

import Control.Monad.Reader
import Control.Monad.State
import LLVM.Prelude hiding (Const)
import LLVM.AST hiding (args, Type, Ret, Operand, Terminator)
import qualified LLVM.AST as LL
import qualified LLVM.AST.AddrSpace as LLAddr
import qualified LLVM.AST.Typed as LL
import qualified LLVM.AST.CallingConvention as LL
import LLVM.AST.DataLayout
import qualified LLVM.AST.Float as LL
import qualified LLVM.AST.Global as LLGlob
import qualified LLVM.AST.Linkage as LL
import qualified LLVM.AST.ParameterAttribute as LL
import qualified LLVM.AST.Type as LL
import qualified LLVM.AST.Visibility as LLVis
import qualified LLVM.AST.Constant as LL
import Data.String
import System.FilePath
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Vector as Vec

import Misc
import Sizeof (variantsTagSize)
import qualified Back.Low as Low
import Back.Low

codegen :: FilePath -> Program -> DataLayout -> ShortByteString -> Module
codegen moduleFilePath (Program fs es gs ts names) layout triple = Module
    { moduleName = fromString (takeBaseName moduleFilePath)
    , moduleSourceFileName = fromString moduleFilePath
    , moduleDataLayout = Just layout
    , moduleTargetTriple = Just triple
    , moduleDefinitions = concat
                              [ defineTypes ts
                              , declareExterns es
                              , declareGlobals names gs
                              -- TODO: init should be part of this already
                              , defineFuns names fs
                              , [defineMain names]
                              ]
    }

-- | How the different sorts of types are represented in LLVM:
--
--   A Unit is represented by a zero-sized array. The reason for using an array is that
--   LLVM did some "optimization" on empty structs that broke tail recursion when the
--   return type was a zero sized type.
--
--   An Enum is represented as the smallest integer type that can fit all variants.
--
--   A Data is represented by a struct that consists of 2 members: an integer that can fit
--   the variant index as well as "fill" the succeeding space (implied by alignment) until
--   the second member starts, followed by the second member which is an array of integers
--   with integer size equal to the alignment of the greatest aligned variant and array
--   length equal to the smallest n that results in the array being of size >= the size of
--   the largest sized variant.
--
--   The reason we must make sure to "fill" all space in the representing struct is that
--   LLVM may essentially otherwise incorrectly assume that the space is unused and
--   doesn't have to be considered passing the type as an argument to a function.
--
--   The reason we fill it with values the size of the alignment instead of bytes is to
--   not wrongfully signal to LLVM that the padding will be used as-is, and should be
--   passed/returned in its own registers (or whatever exactly is going on). I just know
--   from trial and error when debugging issues with how the representation of `(Maybe
--   Int8)` affects how it is returned from a function. The intuitive definition (which
--   indeed could be used for `Maybe` specifically without problems, since the only other
--   variant is the non-data-carrying `None`) is `{i8, i64}`. Representing it instead with
--   `{i64, i64}` (to make alignment-induced padding explicit, also this is how Rust
--   represents it) works well -- it seems to be passed/returned in exactly the same
--   way. However, if we represent it as `{i8, [7 x i8], i64}` or `{i8, [15 x i8], [0 x
--   i64]}`: while having the same size and alignment, it is not returned in the same way
--   (seeming instead to use an additional return parameter), and as such, a Carth
--   function returning `(Maybe Int8)` represented as `{i8, [15 x i8], [0 x i64]}` is not
--   ABI compatible with a Rust function returning `Maybe<i8>` represented as `{i64,
--   i64}`.
defineTypes :: TypeDefs -> [Definition]
defineTypes = (=<<) define . Vec.toList
  where
    define :: TypeDef -> [Definition]
    define = \case
        Enum _ _ -> []
        Struct name ms ->
            [TypeDefinition (mkName name) (Just (structType (map genType ms)))]
        Data' (Data name vs aMax sMax) ->
            let sTag = max (fromJust (variantsTagSize vs)) aMax
                tag = IntegerType (8 * fromIntegral sTag)
                fill = ArrayType (fromIntegral (div (sMax + aMax - 1) aMax))
                                 (IntegerType (8 * fromIntegral aMax))
            in  [TypeDefinition (mkName name) (Just (structType [tag, fill]))]

declareExterns :: [ExternDecl] -> [Definition]
declareExterns = map declare
  where
    declare (ExternDecl name ps r) =
        let
            anon = mkName ""
            (f, rt) = case r of
                RetVal t -> (id, genType t)
                RetVoid -> (id, LL.void)
                OutParam t ->
                    ((Parameter (LL.ptr (genType t)) anon [LL.SRet] :), LL.void)
            ps' = f $ flip map ps $ \case
                ByVal () t -> Parameter (genType t) anon []
                ByRef () t -> Parameter (LL.ptr (genType t)) anon [LL.ByVal]
        in
            simpleFun LL.External name ps' rt []

simpleFun :: LL.Linkage -> String -> [Parameter] -> LL.Type -> [BasicBlock] -> Definition
simpleFun link n ps rt bs = GlobalDefinition $ Function
    { LLGlob.linkage = link
    , LLGlob.visibility = LLVis.Default
    , LLGlob.dllStorageClass = Nothing
    , LLGlob.callingConvention = LL.C
    , LLGlob.returnAttributes = []
    , LLGlob.returnType = rt
    , LLGlob.name = mkName n
    , LLGlob.parameters = (ps, False)
    , LLGlob.functionAttributes = []
    , LLGlob.section = Nothing
    , LLGlob.comdat = Nothing
    , LLGlob.alignment = 0
    , LLGlob.garbageCollectorName = Nothing
    , LLGlob.prefix = Nothing
    , LLGlob.basicBlocks = bs
    , LLGlob.personalityFunction = Nothing
    , LLGlob.metadata = []
    }

declareGlobals :: VarNames -> [GlobDef] -> [Definition]
declareGlobals names = map declare
  where
    declare g =
        let (isconst, ident, initializer) = case g of
                GVarDef (Global x t) _ _ -> (False, x, LL.Undef (genType t))
                GConstDef (Global x _) c -> (True, x, genConst c)
        in  GlobalDefinition $ GlobalVariable { LLGlob.name = mkName (getName names ident)
                                              , LLGlob.linkage = LL.Private
                                              , LLGlob.visibility = LLVis.Default
                                              , LLGlob.dllStorageClass = Nothing
                                              , LLGlob.threadLocalMode = Nothing
                                              , LLGlob.addrSpace = LLAddr.AddrSpace 0
                                              , LLGlob.unnamedAddr = Nothing
                                              , LLGlob.isConstant = isconst
                                              , LLGlob.type' = LL.typeOf initializer
                                              , LLGlob.initializer = Just initializer
                                              , LLGlob.section = Nothing
                                              , LLGlob.comdat = Nothing
                                              , LLGlob.alignment = 0
                                              , LLGlob.metadata = []
                                              }

genConst :: Const -> LL.Constant
genConst = \case
    Undef t -> LL.Undef (genType t)
    I8 n -> LL.Int 8 (fromIntegral n)
    I16 n -> LL.Int 16 (fromIntegral n)
    I32 n -> LL.Int 32 (fromIntegral n)
    I64 n -> LL.Int 64 (fromIntegral n)
    F32 x -> LL.Float (LL.Single x)
    F64 x -> LL.Float (LL.Double x)
    Array t xs -> LL.Array (genType t) (map genConst xs)
    Zero t -> case genType t of
        t'@(LL.PointerType _ _) -> LL.Null t'
        t' -> LL.AggregateZero t'

getName :: VarNames -> Word -> String
getName ns i = ns Vec.! fromIntegral i

defineFuns :: VarNames -> [FunDef] -> [Definition]
defineFuns gnames = map define
  where
    define (FunDef ident ps r block lnames) =
        let
            (f, rt) = case r of
                RetVal t -> (id, genType t)
                RetVoid -> (id, LL.void)
                OutParam t ->
                    ((Parameter (LL.ptr (genType t)) (mkName "out") [LL.SRet] :), LL.void)
            ps' = f $ flip map ps $ \case
                ByVal x t -> Parameter (genType t) (mkName (getName lnames x)) []
                ByRef x t ->
                    Parameter (LL.ptr (genType t)) (mkName (getName lnames x)) [LL.ByVal]
        in
            simpleFun LL.Internal (getName gnames ident) ps' rt (run (genBlock block))

type St = ()
type Gen = State St

run :: Gen () -> [BasicBlock]
run = _

class GenBlock a where
    type Out a
    genBlock :: Block a -> Gen (Out a)

instance GenBlock Terminator where
    type Out Terminator = ()
    genBlock = _

-- TODO: In this incarnation, this outermost main should just call init and
--       user-main. init will in turn init global vars & setup stack overflow handler etc.
defineMain :: VarNames -> Definition
defineMain gnames = simpleFun LL.External "main" [] LL.i32 $ pure $ BasicBlock
    (mkName "entry")
    [ LL.Do (callNamed "install_stackoverflow_handler" [] LL.void)
    , LL.Do (callNamed "carth_init" [] LL.void)
    , LL.Do (callNamed "carth_main" [] LL.void)
    ]
    (LL.Do (LL.Ret (Just (ConstantOperand (LL.Int 32 0))) []))

genType :: Type -> LL.Type
genType = \case
    TI8 -> LL.IntegerType 8
    TI16 -> LL.IntegerType 16
    TI32 -> LL.IntegerType 32
    TI64 -> LL.IntegerType 64
    TF32 -> LL.FloatingPointType LL.FloatFP
    TF64 -> LL.FloatingPointType LL.DoubleFP
    TPtr u -> LL.ptr (genType u)
    TFun ps r ->
        let (f, rt) = case r of
                RetVal t -> (id, genType t)
                RetVoid -> (id, LL.void)
                OutParam t -> ((LL.ptr (genType t) :), LL.void)
        in  LL.FunctionType rt (f (map genParam ps)) False
    TConst i -> _
  where
    genParam = \case
        ByVal () pt -> genType pt
        ByRef () pt -> LL.ptr (genType pt)

structType :: [LL.Type] -> LL.Type
structType ts = StructureType { isPacked = False, elementTypes = ts }

callNamed :: String -> [LL.Operand] -> LL.Type -> Instruction
callNamed f as rt =
    let f' = ConstantOperand $ LL.GlobalReference
            (LL.ptr (FunctionType rt (map LL.typeOf as) False))
            (mkName f)
    in  call f' (map (, []) as)

call :: LL.Operand -> [(LL.Operand, [LL.ParameterAttribute])] -> Instruction
call f as = LL.Call { tailCallKind = Just NoTail
                    , callingConvention = LL.C
                    , returnAttributes = []
                    , function = Right f
                    , arguments = as
                    , functionAttributes = []
                    , metadata = []
                    }
