module Sizeof (sizeof, toBytes, toBits, wordsize, wordsizeBits, tagBits, tagBytes, variantsTagBits, variantsTagBytes) where

import Data.Foldable
import qualified Data.Map as Map
import qualified Data.Vector as Vec
import Data.Vector (Vector)
import Data.Word

import Misc
import Front.Inferred (TypeDefs, Type (..), TPrim (..), Span)
import Front.Subst

-- TODO: Handle different data layouts. Check out LLVMs DataLayout class and impl of
--       `getTypeAllocSize`.  https://llvm.org/doxygen/classllvm_1_1DataLayout.html
--
-- See the [System V ABI docs](https://refspecs.linuxbase.org/elf/x86_64-abi-0.99.pdf) for more
-- info.
sizeof :: TypeDefs -> Type -> Maybe Word32
sizeof datas = \case
    TVar _ -> Nothing
    TConst x -> sizeofData (lookupDatatype x)
    TPrim (TNat nbits) -> Just (toBytes nbits)
    TPrim (TInt nbits) -> Just (toBytes nbits)
    -- integer sized to fit a pointer, which is of word size (right?)
    TPrim TNatSize -> Just wordsize
    TPrim TIntSize -> Just wordsize
    TPrim TF32 -> Just (toBytes 32)
    TPrim TF64 -> Just (toBytes 64)
    -- pointer to captures struct + function pointer, word alignment => no padding
    TFun _ _ -> Just (2 * wordsize)
    TBox _ -> Just wordsize -- single pointer
  where
    lookupDatatype (x, args) = case Map.lookup x datas of
        Just (params, variants) ->
            let sub = Map.fromList (zip params args) in map (map (subst sub) . snd) variants
        Nothing -> ice $ "Infer.lookupDatatype: undefined datatype " ++ show x

    sizeofData :: [[Type]] -> Maybe Word32
    sizeofData = fmap (maximumOr 0) . mapM sizeofStruct . tagUnion

    sizeofStruct :: [Type] -> Maybe Word32
    sizeofStruct ts = do
        (s, a) <- foldlM addMember (0, 1) ts
        pure $ s + (mod (a - s) a)
      where
        addMember :: (Word32, Word32) -> Type -> Maybe (Word32, Word32)
        addMember (accSize, maxAlign) t = do
            a <- alignmentof t
            let padding = if a == 0 then 0 else mod (a - accSize) a
            size <- sizeof datas t
            Just (accSize + padding + size, max a maxAlign)

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
    tagVariant span ts = if span <= 1 then ts else (TPrim (TNat (tagBits span)) : ts)

toBytes :: Integral n => n -> n
toBytes n = div (n + 7) 8

toBits :: Integral n => n -> n
toBits n = 8 * n

wordsize :: Integral n => n
wordsize = toBytes wordsizeBits

wordsizeBits :: Integral n => n
wordsizeBits = 64 -- TODO: Make platform dependent

variantsTagBytes :: Integral n => Vector a -> n
variantsTagBytes = toBytes . variantsTagBits

variantsTagBits :: Integral n => Vector a -> n
variantsTagBits = tagBits . fromIntegral . Vec.length

tagBytes :: Integral n => Span -> n
tagBytes = toBytes . tagBits

tagBits :: Integral n => Span -> n
tagBits span | span <= 2 ^ (0 :: Integer) = ice $ "tagBits: span = " ++ show span
             | span <= 2 ^ (8 :: Integer) = 8
             | span <= 2 ^ (16 :: Integer) = 16
             | span <= 2 ^ (32 :: Integer) = 32
             | span <= 2 ^ (64 :: Integer) = 64
             | otherwise = ice $ "tagBits: span = " ++ show span
