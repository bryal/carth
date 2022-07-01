-- | Generation of LLVM IR code from our monomorphic AST.
module Back.CompileC (compile) where

import Control.Arrow
import Data.Graph (flattenSCCs, stronglyConnComp)
import Data.Maybe
import Data.List
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import System.FilePath
import System.Process

import Back.Low
import Conf
import Misc

compile :: FilePath -> CompileConfig -> Program -> IO ()
compile f cfg pgm = do
    let exefile = cOutfile cfg
        cfile = replaceExtension exefile "c"
    let cSrc = codegen pgm
    putStrLn ("\n\n" ++ cSrc ++ "\n")
    writeFile cfile cSrc
    callProcess
        (cCompiler cfg)
        [ "-o"
        , exefile
        , cfile
        , "-l:libcarth_std_rs.a"
        , "-lsigsegv"
        , "-ldl"
        , "-lpthread"
        , "-lm"
        , "-lgc"
        , "-lssl"
        , "-lcrypto"
        ]
    putStrLn "C backend not yet complete"
    abort f

codegen :: Program -> String
codegen (Program _fdefs _edecls _gdefs tdefs _gnames _main) = unlines
    [ "#include <stdint.h>"
    , ""
    , declareTypes
    , ""
    , defineTypes
    ]
  where
    tdefs' = Vec.fromList (resolveTypeNameConflicts (map (first replaceInvalidIdentChars) tdefs))

    replaceInvalidIdentChars =
        map $ \c -> if ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9')
            then c
            else '_'

    declareTypes = intercalate "\n" (map (uncurry declareType) orderedTypes)

    declareType name d =
        "typedef "
            ++ case d of
                   DEnum _ -> "enum"
                   DStruct _ -> "struct"
                   DUnion _ -> "union"
            ++ " "
            ++ name
            ++ " "
            ++ name
            ++ ";"

    defineTypes = intercalate "\n\n" (map (uncurry defineType) orderedTypes)

    defineType name = \case
        DEnum vs ->
            "enum "
                ++ name
                ++ " {"
                ++ precalate "\n    " (map genEnumVariant (Vec.toList vs))
                ++ "\n};"
        DStruct struct ->
            "struct "
                ++ name
                ++ " {"
                ++ precalate "\n    " (map genStructMember (structMembers struct))
                ++ "\n};"
        DUnion union ->
            "union "
                ++ name
                ++ " {"
                ++ precalate "\n    " (mapMaybe genUnionVariant (Vec.toList (unionVariants union)))
                ++ "\n};"
      where
        genEnumVariant v = v ++ ","
        genStructMember (x, t) = genType tdefs' t (genMember x) ++ ";"
        genUnionVariant = \case
            (x, Sized ti) -> Just (typeName tdefs' ti ++ " " ++ x ++ ";")
            _ -> Nothing

    -- We have to declare & define types in C in a certain order, depending on when they are
    -- used. For example, if some struct Foo has a field which type is another struct Bar, then Bar
    -- must be *defined* before Foo. On the other hand, if Bar has a field which is a pointer to
    -- Foo, then Foo must be *declared* before Bar is *defined*.
    orderedTypes = flattenSCCs (stronglyConnComp graph)
      where
        graph = zipWith (\tid def -> (def, tid, Set.toList (directTypeDeps (snd def))))
                        [0 :: Word ..]
                        (Vec.toList tdefs')
        directTypeDeps = \case
            DEnum _ -> Set.empty
            DStruct struct -> Set.unions
                (map
                    (snd >>> \case
                        TConst tid -> Set.singleton tid
                        TClosure{} -> Set.singleton (asTConst (builtinType "closure"))
                        _ -> Set.empty
                    )
                    (structMembers struct)
                )
            DUnion union -> Set.unions
                (map (sized Set.empty Set.singleton . snd) (Vec.toList (unionVariants union)))

    genMember (MemberId i) = "m" ++ show i

genType :: Vector TypeDef -> Type -> String -> String
genType tdefs t x = case t of
    TInt width -> "int" ++ show width ++ "_t " ++ x
    TNat width -> "uint" ++ show width ++ "_t " ++ x
    TF32 -> "float " ++ x
    TF64 -> "double " ++ x
    TPtr t -> genType tdefs t ("(*" ++ x ++ ")")
    VoidPtr -> "void *" ++ x
    TFun outParam params ret ->
        maybe (genRet ret) (genType tdefs . outParamType) outParam
            $ "(*"
            ++ x
            ++ ")("
            ++ intercalate ", " (map genAnonParam params)
            ++ ")"
    TConst ti -> typeName tdefs ti ++ " " ++ x
    TArray t n -> genType tdefs t (x ++ "[" ++ show n ++ "]")
    TClosure{} -> genType tdefs (builtinType "closure") x
  where
    genAnonParam p = genType tdefs (paramType p) ""
    genRet = \case
        RetVal t -> genType tdefs t
        RetVoid -> ("void " ++)
