{-# LANGUAGE ScopedTypeVariables, AllowAmbiguousTypes #-}

module Sizeof where

import Data.Foldable
import qualified Data.Vector as Vec
import Data.Vector (Vector)

import Misc
import Front.Inferred (Span)
import Front.TypeAst

type SizeofConst tvar = TConst' tvar -> Either tvar Word
type AlignofConst tvar = TConst' tvar -> Either tvar Word

-- TODO: Handle different data layouts. Check out LLVMs DataLayout class and impl of
--       `getTypeAllocSize`.  https://llvm.org/doxygen/classllvm_1_1DataLayout.html
--
-- See the [System V ABI docs](https://refspecs.linuxbase.org/elf/x86_64-abi-0.99.pdf) for more
-- info.
sizeof :: forall tvar . SizeofConst tvar -> Type' tvar -> Either tvar Word
sizeof siConst = \case
    TVar tv -> Left tv
    TConst x -> siConst x
    TPrim tp -> Right $ sizeofTPrim tp
    -- pointer to captures struct + function pointer
    TFun _ _ -> Right (2 * wordsize)
    TBox _ -> Right wordsize -- single pointer

sizeofData :: SizeofConst tvar -> AlignofConst tvar -> [[Type' tvar]] -> Either tvar Word
sizeofData siConst alConst = \case
    [] -> Right 0
    [ts] -> sizeofStruct siConst alConst ts
    vs -> do
        tag <- alignmentofData alConst vs
        maxStruct <- maximumOr 0 <$> mapM (sizeofStruct siConst alConst) vs
        Right (tag + maxStruct)

sizeofStruct
    :: forall tvar . SizeofConst tvar -> AlignofConst tvar -> [Type' tvar] -> Either tvar Word
sizeofStruct siConst alConst ts = do
    (s, a) <- foldlM addMember (0, 1) ts
    pure $ s + mod (a - s) a
  where
    addMember :: (Word, Word) -> Type' tvar -> Either tvar (Word, Word)
    addMember (accSize, maxAlign) t = do
        a <- alignmentof alConst t
        let padding = if a == 0 then 0 else mod (a - accSize) a
        size <- sizeof siConst t
        Right (accSize + padding + size, max a maxAlign)

alignmentof :: forall tvar . AlignofConst tvar -> Type' tvar -> Either tvar Word
alignmentof alConst = \case
    TVar tv -> Left tv
    TConst x -> alConst x
    TFun _ _ -> Right wordsize
    TBox _ -> Right wordsize
    TPrim tp -> Right $ sizeofTPrim tp

sizeofTPrim :: TPrim -> Word
sizeofTPrim = \case
    TNat nbits -> toBytes (fromIntegral nbits)
    TInt nbits -> toBytes (fromIntegral nbits)
    -- integer sized to fit a pointer, which is of word size (right?)
    TNatSize -> wordsize
    TIntSize -> wordsize
    TF32 -> toBytes 32
    TF64 -> toBytes 64

alignmentofData :: AlignofConst tvar -> [[Type' tvar]] -> Either tvar Word
alignmentofData alConst vs = do
    let aTag = tagBytes (fromIntegral (length vs))
    as <- mapM (alignmentofStruct alConst) vs
    pure (max aTag (maximumOr 0 as))

alignmentofStruct :: AlignofConst tvar -> [Type' tvar] -> Either tvar Word
alignmentofStruct alConst = fmap (maximumOr 0) . mapM (alignmentof alConst)

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
tagBits span | span <= 2 ^ (0 :: Integer) = 0
             | span <= 2 ^ (8 :: Integer) = 8
             | span <= 2 ^ (16 :: Integer) = 16
             | span <= 2 ^ (32 :: Integer) = 32
             | span <= 2 ^ (64 :: Integer) = 64
             | otherwise = ice $ "tagBits: span = " ++ show span
