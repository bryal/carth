{-# LANGUAGE LambdaCase #-}

-- | Stuff relating to structure layout and calling convention
--
--   One might think that simply declaring all function definitions and function
--   calls as being of the same LLVM calling convention (e.g. "ccc") would allow
--   us to pass arguments and return results as we please, and everything will
--   be compatible? I sure did, however, that is not the case. To be compatible
--   with C FFIs, we also have to actually conform to the C calling convention,
--   which contains a bunch of details about how more complex types should be
--   passed and returned. Currently, we pass and return simple types by value,
--   and complex types by reference (param by ref, return via sret param).
--
--   See the definition of `passByRef` for up-to-date details about which types
--   are passed how.
module Abi
    ( simpleFunc
    , simpleGlobVar
    , simpleGlobVar'
    , passByRef
    , passByRef'
    , sizeof
    , tagBitWidth
    , cfg_callConv
    )
where

import LLVM.Prelude (ShortByteString)
import LLVM.AST
import qualified LLVM.AST.CallingConvention as LLCallConv
import qualified LLVM.AST.Linkage as LLLink
import qualified LLVM.AST.Visibility as LLVis
import qualified LLVM.AST.Constant as LLConst
import qualified LLVM.AST.Global as LLGlob
import qualified LLVM.AST.AddrSpace as LLAddr
import Control.Monad.Writer
import qualified Data.Map as Map
import Data.Word
import Data.Foldable
import Lens.Micro.Platform (view, to)

import Misc
import Monomorphic (Span)
import Gen


simpleFunc
    :: Name
    -> [Parameter]
    -> Type
    -> [BasicBlock]
    -> [(ShortByteString, MDRef MDNode)]
    -> Global
simpleFunc n ps rt bs meta = Function
    { LLGlob.linkage = LLLink.External
    , LLGlob.visibility = LLVis.Default
    , LLGlob.dllStorageClass = Nothing
    , LLGlob.callingConvention = cfg_callConv
    , LLGlob.returnAttributes = []
    , LLGlob.returnType = rt
    , LLGlob.name = n
    , LLGlob.parameters = (ps, False)
    , LLGlob.functionAttributes = []
    , LLGlob.section = Nothing
    , LLGlob.comdat = Nothing
    , LLGlob.alignment = 0
    , LLGlob.garbageCollectorName = Nothing
    , LLGlob.prefix = Nothing
    , LLGlob.basicBlocks = bs
    , LLGlob.personalityFunction = Nothing
    , LLGlob.metadata = meta
    }

simpleGlobVar :: Name -> Type -> LLConst.Constant -> Global
simpleGlobVar name t = simpleGlobVar' name t . Just

simpleGlobVar' :: Name -> Type -> Maybe LLConst.Constant -> Global
simpleGlobVar' name t initializer = GlobalVariable
    { LLGlob.name = name
    , LLGlob.linkage = LLLink.External
    , LLGlob.visibility = LLVis.Default
    , LLGlob.dllStorageClass = Nothing
    , LLGlob.threadLocalMode = Nothing
    , LLGlob.addrSpace = LLAddr.AddrSpace 0
    , LLGlob.unnamedAddr = Nothing
    , LLGlob.isConstant = True
    , LLGlob.type' = t
    , LLGlob.initializer = initializer
    , LLGlob.section = Nothing
    , LLGlob.comdat = Nothing
    , LLGlob.alignment = 0
    , LLGlob.metadata = []
    }

passByRef :: Type -> Gen Bool
passByRef = lift . passByRef'

-- NOTE: This post is helpful:
--       https://stackoverflow.com/questions/42411819/c-on-x86-64-when-are-structs-classes-passed-and-returned-in-registers
--       Also, official docs:
--       https://software.intel.com/sites/default/files/article/402129/mpx-linux64-abi.pdf
--       particularly section 3.2.3 Parameter Passing (p18).
passByRef' :: Type -> Gen' Bool
passByRef' = \case
    NamedTypeReference x -> view (dataTypes . to (Map.lookup x)) >>= \case
        Just ts -> passByRef' (typeStruct ts)
        Nothing ->
            ice $ "passByRef': No dataType for NamedTypeReference " ++ show x
    -- Simple scalar types. They go in registers.
    VoidType -> pure False
    IntegerType _ -> pure False
    PointerType _ _ -> pure False
    FloatingPointType _ -> pure False
    -- Functions are not POD (Plain Ol' Data), so they are passed on the stack.
    FunctionType _ _ _ -> pure True
    -- TODO: Investigate how exactly SIMD vectors are to be passed when/if we
    --       ever add support for that in the rest of the compiler.
    VectorType _ _ -> pure True
    -- Aggregate types can either be passed on stack or in regs, depending on
    -- what they contain.
    t@(StructureType _ us) -> do
        size <- sizeof t
        if size > 16 then pure True else fmap or (mapM passByRef' us)
    ArrayType _ u -> do
        size <- sizeof u
        if size > 16 then pure True else passByRef' u
    -- N/A
    MetadataType -> ice "passByRef of MetadataType"
    LabelType -> ice "passByRef of LabelType"
    TokenType -> ice "passByRef of TokenType"

-- TODO: Handle packed
--
-- TODO: Handle different data layouts. Check out LLVMs DataLayout class and
--       impl of `getTypeAllocSize`.
--       https://llvm.org/doxygen/classllvm_1_1DataLayout.html
--
-- | Haskell-native implementation of `sizeof`, in contrast to
--   `getTypeAllocSize` of `llvm-hs`.
--
--   The problem with `getTypeAllocSize` is that it requires an `EncodeAST`
--   monad and messy manipulations. Specifically, I had some recursive bindings
--   going on, but to represent them in a monad I needed `mfix`, but `EncodeAST`
--   didn't have `mfix`!
--
--   See the [System V ABI docs](https://software.intel.com/sites/default/files/article/402129/mpx-linux64-abi.pdf)
--   for more info.
sizeof :: Type -> Gen' Word64
sizeof = \case
    NamedTypeReference x -> sizeof =<< lookupDatatype x
    IntegerType bits -> pure (fromIntegral (toBytesCeil bits))
    PointerType _ _ -> pure 8
    FloatingPointType HalfFP -> pure 2
    FloatingPointType FloatFP -> pure 4
    FloatingPointType DoubleFP -> pure 8
    FloatingPointType FP128FP -> pure 16
    FloatingPointType X86_FP80FP -> pure 16
    FloatingPointType PPC_FP128FP -> pure 16
    StructureType _ us -> foldlM addMember 0 us
    VectorType n u -> fmap (fromIntegral n *) (sizeof u)
    ArrayType n u -> fmap (n *) (sizeof u)
    VoidType -> ice "sizeof VoidType"
    FunctionType _ _ _ -> ice "sizeof FunctionType"
    MetadataType -> ice "sizeof MetadataType"
    LabelType -> ice "sizeof LabelType"
    TokenType -> ice "sizeof TokenType"
  where
    toBytesCeil nbits = div (nbits + 7) 8
    addMember accSize u = do
        align <- alignmentof u
        let padding = if align == 0 then 0 else mod (align - accSize) align
        size <- sizeof u
        pure (accSize + padding + size)

alignmentof :: Type -> Gen' Word64
alignmentof = \case
    NamedTypeReference x -> alignmentof =<< lookupDatatype x
    StructureType _ [] -> pure 0
    t@(StructureType _ us) -> do
        as <- traverse alignmentof us
        if null as
            then ice ("alignmentof: alignments empty for struct " ++ show t)
            else pure (maximum as)
    VectorType _ u -> alignmentof u
    ArrayType _ u -> alignmentof u
    t -> sizeof t

tagBitWidth :: Span -> Maybe Word32
tagBitWidth span'
    | span' <= 2 ^ (0 :: Integer) = Nothing
    | span' <= 2 ^ (8 :: Integer) = Just 8
    | span' <= 2 ^ (16 :: Integer) = Just 16
    | span' <= 2 ^ (32 :: Integer) = Just 32
    | span' <= 2 ^ (64 :: Integer) = Just 64
    | otherwise = ice $ "tagBitWidth: span' = " ++ show span'

-- TODO: Try out "tailcc" - Tail callable calling convention. It looks like
--       exactly what I want!
cfg_callConv :: LLCallConv.CallingConvention
cfg_callConv = LLCallConv.C
