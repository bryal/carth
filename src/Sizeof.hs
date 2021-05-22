module Sizeof (sizeof, toBytes, wordsize, wordsizeBits, tagBitWidth) where

import Data.Foldable
import qualified Data.Map as Map
import Data.Word

import Misc
import Front.Inferred (TypeDefs, Type (..), TPrim (..), Span)
import Front.Subst

-- TODO: Handle different data layouts. Check out LLVMs DataLayout class and impl of
--       `getTypeAllocSize`.  https://llvm.org/doxygen/classllvm_1_1DataLayout.html
--
-- See the [System V ABI docs](https://software.intel.com/sites/default/files/article/402129/mpx-linux64-abi.pdf)
-- for more info.
sizeof :: TypeDefs -> Type -> Maybe Word32
sizeof datas = \case
    TVar _ -> Nothing
    TConst x -> sizeofData (lookupDatatype x)
    TPrim (TNat nbits) -> Just (toBytes nbits)
    TPrim (TInt nbits) -> Just (toBytes nbits)
    -- integer sized to fit a pointer, which is of word size (right?)
    TPrim TNatSize -> Just wordsize
    TPrim TIntSize -> Just wordsize
    TPrim TF16 -> Just (toBytes 16)
    TPrim TF32 -> Just (toBytes 32)
    TPrim TF64 -> Just (toBytes 64)
    TPrim TF128 -> Just (toBytes 128)
    -- pointer to captures struct + function pointer, word alignment => no padding
    TFun _ _ -> Just (2 * wordsize)
    TBox _ -> Just wordsize -- single pointer
  where
    lookupDatatype (x, args) = case Map.lookup x datas of
        Just (params, variants) ->
            let sub = Map.fromList (zip params args)
            in  map (map (subst sub) . snd) variants
        Nothing -> ice $ "Infer.lookupDatatype: undefined datatype " ++ show x

    sizeofData :: [[Type]] -> Maybe Word32
    sizeofData = fmap (maximumOr 0) . mapM sizeofStruct . tagUnion

    sizeofStruct :: [Type] -> Maybe Word32
    sizeofStruct = foldlM addMember 0
      where
        addMember :: Word32 -> Type -> Maybe Word32
        addMember accSize t = do
            a <- alignmentof t
            let padding = if a == 0 then 0 else mod (a - accSize) a
            size <- sizeof datas t
            Just (accSize + padding + size)

    alignmentof :: Type -> Maybe Word32
    alignmentof = \case
        TVar _ -> Nothing
        TConst x -> alignmentofData (lookupDatatype x)
        t -> sizeof datas t

    alignmentofData :: [[Type]] -> Maybe Word32
    alignmentofData = fmap (maximumOr 0) . mapM alignmentofStruct . tagUnion

    alignmentofStruct :: [Type] -> Maybe Word32
    alignmentofStruct = fmap (maximumOr 0) . mapM alignmentof

    tagUnion :: [[Type]] -> [[Type]]
    tagUnion vs = map (tagVariant (fromIntegral (length vs))) vs

    tagVariant :: Span -> [Type] -> [Type]
    tagVariant span ts = maybe ts ((: ts) . TPrim . TNat) (tagBitWidth span)

toBytes :: Integral n => n -> n
toBytes n = div (n + 7) 8

wordsize :: Integral n => n
wordsize = toBytes wordsizeBits

wordsizeBits :: Integral n => n
wordsizeBits = 64 -- TODO: Make platform dependent

tagBitWidth :: Integral n => Span -> Maybe n
tagBitWidth span | span <= 2 ^ (0 :: Integer) = Nothing
                 | span <= 2 ^ (8 :: Integer) = Just 8
                 | span <= 2 ^ (16 :: Integer) = Just 16
                 | span <= 2 ^ (32 :: Integer) = Just 32
                 | span <= 2 ^ (64 :: Integer) = Just 64
                 | otherwise = ice $ "tagBitWidth: span = " ++ show span
