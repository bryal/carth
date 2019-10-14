module SizeOf (sizeof, dataLayout) where

import Data.Word
import LLVM.AST.Type
import LLVM.AST.DataLayout
import LLVM.Context
import LLVM.Internal.DataLayout (withFFIDataLayout)
import LLVM.Internal.FFI.DataLayout (getTypeAllocSize)
import qualified LLVM.Internal.FFI.PtrHierarchy as LLPtrHierarchy
import qualified LLVM.Internal.Coding as LLCoding
import qualified LLVM.Internal.EncodeAST as LLEncode
import qualified LLVM.Internal.Type ()
import qualified Foreign.Ptr

type FFIType = Foreign.Ptr.Ptr LLPtrHierarchy.Type

sizeof :: Context -> Type -> IO Word64
sizeof ctx t = do
    t' <- toFFIType ctx t
    withFFIDataLayout dataLayout (flip getTypeAllocSize t')

toFFIType :: Context -> Type -> IO FFIType
toFFIType ctx t = LLEncode.runEncodeAST ctx (LLCoding.encodeM t)

dataLayout :: DataLayout
dataLayout = defaultDataLayout LittleEndian
