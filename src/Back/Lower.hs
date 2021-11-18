module Back.Lower (lower, builtinExterns) where

import Data.Bifunctor
import Data.Function
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Vector (Vector)
import qualified Data.Vector as Vec

import qualified Back.Low as Low
import Front.Monomorphic
import Misc
import Sizeof

type TypeEnv = Vector Low.TypeDef
type TypeIds = Map TConst Word

data SizedType = ZeroSized | Sized Low.Type

lower :: Program -> Low.Program
lower (Program _Defs datas externs) =
    let externNames = map (\(name, _, _) -> name) externs
        globNames = _
    in  Low.Program _FunDefs
                    (lowerExterns externs)
                    _GlobDefs
                    tenv
                    (resolveNameConflicts globNames externNames)
  where
    resolveNameConflicts :: [String] -> [String] -> Vector String
    resolveNameConflicts = _


    -- Iff a TConst is zero sized, it will have no entry in tenv & tids
    tenv :: TypeEnv
    tids :: TypeIds
    (tenv, tids) =
        bimap (Vec.fromList . nameUniquely Low.typeName' Low.setTypeName) Map.fromList
            $ unzip
            $ zipWith (\i (a, b) -> (a, (b, i))) [0 ..]
            $ flip mapMaybe (Map.toList datas)
            $ \(tc@(tname, _), vs) ->
                  let vs' = map (second (mapMaybe (sizedMaybe . genType))) vs
                  in
                      fmap (, tc) $ case vs' of
                          [] -> ice "uninhabited type when creating Lower.tenv"
                          [(_, [])] -> Nothing
                          [(_, ts)] -> Just $ Low.DStruct $ Low.Struct
                              tname
                              ts
                              (alignmentofStruct ts)
                              (sizeofStruct ts)
                          _ | all (null . snd) vs' ->
                              Just $ Low.DEnum tname (Vec.fromList (map fst vs'))
                          _ ->
                              let aMax = maximum $ map (alignmentofStruct . snd) vs'
                                  sMax = maximum $ map (sizeofStruct . snd) vs'
                                  vs'' = Vec.fromList vs'
                                  tagSize = max (variantsTagBytes vs'') aMax
                                  align = tagSize
                                  size = tagSize + div (sMax + aMax - 1) aMax * aMax
                              in  Just $ Low.DData $ Low.Data tname vs'' align size aMax

    nameUniquely :: (a -> String) -> (String -> a -> a) -> [a] -> [a]
    nameUniquely get set =
        ((reverse . fst) .) $ flip foldl ([], Map.empty) $ \(ds, seen) d ->
            let name = get d
                uq n =
                    let name' = if n == 0 then name else name ++ "_" ++ show n
                    in  if Map.findWithDefault 0 name' seen == 0
                            then (name', Map.insert name (n + 1) seen)
                            else uq (n + 1)
                (name', seen') = uq (Map.findWithDefault 0 name seen)
            in  (set name' d : ds, seen')

    sizedMaybe = \case
        ZeroSized -> Nothing
        Sized t -> Just t

    -- Since Carth has no concept of arity > 1 for functions, neither accepting a tuple
    -- nor currying is a perfect translation of an n-ary function. If we for example
    -- require an extern sig to be of the form (Fun (Cons ...) _) and translate that to an
    -- n-ary function, how do we write a signature for a function that actually does
    -- accept a single Carth tuple? No, instead, we should write the sigs in n-ary form,
    -- and generate either a tuple or curry wrapper. I think currying would be better, to
    -- better match how we handle saturated calls and stuff elsewhere.
    lowerExterns = map $ \case
        (name, pts, rt) ->
            Low.ExternDecl name (toParam () . genType =<< pts) (toRet (genType rt))

    toParam name = \case
        ZeroSized -> []
        Sized t -> [if passByRef t then Low.ByRef name t else Low.ByVal name t]

    toRet = \case
        ZeroSized -> Low.RetVoid
        Sized t -> if passByRef t then Low.OutParam t else Low.RetVal t

    -- TODO: Should respect platform ABI. For example wrt size of TNatSize on 32-bit
    --       vs. 64-bit platform.
    --
    -- | The Low representation of a type in expression-context
    genType :: Type -> SizedType
    genType = \case
        TPrim (TNat w) -> genIntT w
        TPrim TNatSize -> genIntT wordsizeBits
        TPrim (TInt w) -> genIntT w
        TPrim TIntSize -> genIntT wordsizeBits
        TPrim TF32 -> Sized Low.TF32
        TPrim TF64 -> Sized Low.TF64
        TFun a r -> Sized $ closureType (genType a) (genType r)
        TBox t -> Sized $ case genType t of
            ZeroSized -> Low.VoidPtr
            Sized t' -> Low.TPtr t'
        TConst tc -> Map.lookup tc tids & \case
            Nothing -> ZeroSized
            Just ix -> Sized $ Low.TConst ix
      where
        genIntT w = if
            | w == 0 -> ZeroSized
            | w <= 8 -> Sized Low.TI8
            | w <= 16 -> Sized Low.TI16
            | w <= 32 -> Sized Low.TI32
            | w <= 64 -> Sized Low.TI64
            | otherwise -> ice "Lower.genType: integral type larger than 64-bit"

        closureType a r = _

    -- NOTE: This post is helpful:
    --       https://stackoverflow.com/questions/42411819/c-on-x86-64-when-are-structs-classes-passed-and-returned-in-registers
    --       Also, official docs:
    --       https://refspecs.linuxbase.org/elf/x86_64-abi-0.99.pdf
    --       particularly section 3.2.3 Parameter Passing (p18).
    --
    --       From SystemV x86-64 ABI:
    --       "The size of each argument gets rounded up to eightbytes."
    --       "the term eightbyte refers to a 64-bit object"
    --       "If the size of an object is larger than four eightbytes, or it contains
    --        unaligned fields, it has class MEMORY"
    --       "If the size of the aggregate exceeds two eightbytes and the first eight-byte
    --        isn’t SSE or any other eightbyte isn’t SSEUP, the whole argument is passed
    --        in memory.""
    --
    --       Essentially, for Carth, I think it's true that all aggregate types of size >
    --       2*8 bytes are passed in memory, and everything else is passed in register. We
    --       could always state that this is the ABI we use, and that it's the user's
    --       responsibility to manually handle the cases where it may clash with the
    --       correct C ABI. Maybe we'll want to revisit this if/when we add support for
    --       SIMD vector types something similarly exotic.
    passByRef :: Low.Type -> Bool
    passByRef t = sizeof t > 2 * 8

    sizeofStruct = foldl addMember 0
      where
        addMember accSize u =
            let align = alignmentof u
                padding = if align == 0 then 0 else mod (align - accSize) align
                size = sizeof u
            in  accSize + padding + size

    sizeof = \case
        Low.TI8 -> 1
        Low.TI16 -> 2
        Low.TI32 -> 4
        Low.TI64 -> 8
        Low.TF32 -> 4
        Low.TF64 -> 8
        Low.TPtr _ -> wordsize
        Low.VoidPtr -> wordsize
        Low.TFun _ _ -> wordsize
        Low.TConst ix -> case tenv Vec.! fromIntegral ix of
            Low.DEnum _ vs -> variantsTagBytes vs
            Low.DStruct s -> Low.structSize s
            Low.DData d -> Low.dataSize d

    alignmentofStruct = maximum . map alignmentof

    alignmentof = \case
        Low.TConst ix -> case tenv Vec.! fromIntegral ix of
            Low.DEnum _ vs -> variantsTagBytes vs
            Low.DStruct s -> Low.structAlignment s
            Low.DData d -> Low.dataAlignment d
        t -> sizeof t

-- | To generate cleaner code, a data-type is only represented as a tagged union (Data) if
--   it has to be. If there is only a single variant, we skip the tag and represent it as
--   a Struct. If the struct also has no members, we simplify it further and represent it
--   as a Unit. If instead the data-type has multiple variants, but no variant has any
--   members, it is represented as an Enum.
-- lowerDatas :: ()
-- lowerDatas = ()

-- builtinExterns :: Map String Type
-- builtinExterns = _
