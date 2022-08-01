-- | Generation of LLVM IR code from our monomorphic AST.
module Back.CompileC (compile) where

import Control.Arrow
import Data.Either
import Data.Graph (flattenSCCs, stronglyConnComp)
import Data.Maybe
import Data.List
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import System.FilePath
import System.Process
import Text.Printf

import Back.Low
import Conf
import Misc
import Sizeof
import Front.Parse (c_validIdentFirst, c_validIdentRest, c_keywords)

compile :: CompileConfig -> Program -> IO ()
compile cfg pgm = do
    let exefile = cOutfile cfg
        cfile = replaceExtension exefile "c"
        ofile = replaceExtension exefile "o"
    let cSrc = codegen pgm
    writeFile cfile cSrc
    verbose cfg "   Compiling Object"
    callProcess (cCompiler cfg)
        . concat
        $ [ if getDebug cfg then ["-g", "-Og", "-Wall", "-Wextra", "-Wno-unused-parameter"] else []
          , ["-c"]
          , ["-o", ofile]
          , [cfile]
          ]

codegen :: Program -> String
codegen (Program fdefs edecls gdefs tdefs_unreplaced gnames_unreplaced main) = unlines
    [ "#include <stdint.h>"
    , "#include <stddef.h>"
    , "#include <stdbool.h>"
    , "\n\n/**** Type Declarations ****/\n"
    , declareTypes
    , "\n\n/**** Type Definitions ****/\n"
    , defineTypes
    , "\n\n/**** Global Variable Declarations & Constant Definitions ****/\n"
    , declareGlobs
    , "\n\n/**** Extern Declarations ****/\n"
    , "extern void install_stackoverflow_handler(void);"
    , declareExterns
    , "\n\n/**** Function Declarations ****/\n"
    , fst declareAndDefineFuns
    , "\n\n/**** Function Definitions ****/\n"
    , snd declareAndDefineFuns
    , "\n\n/**** Main ****/\n"
    , defineMain
    ]
  where
    reserved = "install_stackoverflow_handler" : c_keywords

    tdefs = Vec.fromList $ resolveTypeNameConflicts
        reserved
        (map (first replaceInvalidIdentChars) tdefs_unreplaced)
    tdefsNames = Vec.map fst tdefs

    enames = Vec.fromList (map (\(ExternDecl name _ _ _) -> name) edecls)

    gnames = Vec.fromList $ resolveNameConflicts
        (reserved ++ Vec.toList (tdefsNames Vec.++ enames))
        (Vec.toList (Vec.map replaceInvalidIdentChars gnames_unreplaced))

    replaceInvalidIdentChars = \case
        [] -> ice "empty identifier"
        (c : cs) ->
            (if c_validIdentFirst c then c else '_')
                : map (\c' -> if c_validIdentRest c' then c' else '_') cs

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
        genStructMember (x, t) = genType t (genMember x) ++ ";"
        genUnionVariant = \case
            (x, Sized ti) -> Just (typeName tdefs ti ++ " " ++ x ++ ";")
            _ -> Nothing

    -- We have to declare & define types in C in a certain order, depending on when they are
    -- used. For example, if some struct Foo has a field which type is another struct Bar, then Bar
    -- must be *defined* before Foo. On the other hand, if Bar has a field which is a pointer to
    -- Foo, then Foo must be *declared* before Bar is *defined*.
    orderedTypes = flattenSCCs (stronglyConnComp graph)
      where
        graph = zipWith (\tid def -> (def, tid, Set.toList (directTypeDeps (snd def))))
                        [0 :: Word ..]
                        (Vec.toList tdefs)
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

    declareGlobs = intercalate "\n" (map declareGlob gdefs)

    declareGlob :: GlobDef -> String
    declareGlob = \case
        GlobVarDecl gid t -> genType t (gname gid) ++ ";"
        GlobConstDef gid t c ->
            genType t ("const " ++ gname gid)
                ++ either (const "") (" = " ++) (snd (genConst c))
                ++ ";"

    declareExterns = intercalate "\n" (map declareExtern edecls)

    declareExtern :: ExternDecl -> String
    declareExtern (ExternDecl name outParam params ret) = -- (ExternDecl String (Maybe (OutParam ())) [Param ()] Ret) =
        maybe (genRet tdefs ret)
              (genType . outParamType)
              outParam
              (name ++ "(" ++ intercalate ", " (map (genAnonParam tdefs) params) ++ ")")
            ++ ";"

    declareAndDefineFuns =
        let (decs, defs) = unzip (map defineFun fdefs)
        in  (intercalate "\n" decs, intercalate "\n\n" defs)

    -- Returns both declaration & definition
    defineFun (FunDef name out params ret body allocs' lnames_unreplaced) =
        let lhs = maybe
                (genRet tdefs ret)
                (genType . outParamType)
                out
                (gname name ++ "(" ++ intercalate ", " (map (genParam lnames) params) ++ ")")
            rhs =
                " {"
                    ++ precalate "\n    " (map genAlloc allocs)
                    ++ (if null allocs then "" else "\n    ")
                    ++ genBlock' 4 genTerm body
                    ++ "\n}"
        in  (lhs ++ ";", lhs ++ rhs)
      where
        allocs = maybe id (\(OutParam x t) -> ((x, t) :)) out allocs'

        localIsAlloc lid = Set.member lid localAllocs
        localAllocs = Set.fromList (map fst allocs)

        genAlloc (lid, t) = genType t (lname' lid) ++ ";"

        lname' = lname lnames

        lnames = Vec.fromList $ resolveNameConflicts
            (reserved ++ Vec.toList (tdefsNames Vec.++ enames Vec.++ gnames))
            (Vec.toList (Vec.map replaceInvalidIdentChars lnames_unreplaced))

        genBlock :: Int -> (Int -> term -> String) -> Block term -> String
        genBlock d genTerm' blk = "{" ++ genBlock' (d + 4) genTerm' blk ++ "\n" ++ indent d ++ "}"

        genBlock' :: Int -> (Int -> term -> String) -> Block term -> String
        genBlock' d genTerm' (Block stms term) =
            precalate ("\n" ++ indent d) (map (genStm d) stms) ++ case genTerm' d term of
                "" -> ""
                s -> "\n" ++ indent d ++ s

        genTerm d = \case
            TRetVal e -> genExpr d (\val -> "return " ++ val ++ ";") e
            TRetVoid | Just (OutParam x _) <- out -> "return " ++ lname' x ++ ";"
                     | otherwise -> "return;"

        genStm d = \case
            Let (Local x t) e ->
                let e' = genExpr (d + 4) (\val -> lname' x ++ " = " ++ val ++ ";") e
                in  genType t (lname' x)
                        ++ if (lname' x ++ " = ") `isPrefixOf` e' && length (lines e') == 1
                               then drop (length (lname' x)) e'
                               else ";\n" ++ indent d ++ e'
            Store x dst -> either (const "")
                                  (((snd (preop "*" (genOp' dst)) ++ " = ") ++) . (++ ";"))
                                  (snd (genOp x))
            VoidCall f out' as ->
                maybe "" (\o -> snd (preop "*" (genOp' o)) ++ " = ") out'
                    ++ snd (binop_call (genOp' f) (map (snd . genOp') as))
                    ++ ";"
            SLoop lp -> genLoop d (\_ () -> "break;") lp
            SBranch br -> genBranch d (\_ () -> "") br
        genBranch :: Int -> (Int -> term -> String) -> Branch term -> String
        genBranch d genTerm' = \case
            BIf p c a ->
                ("if (" ++ snd (genOp' p) ++ ") ")
                    ++ genBlock d genTerm' c
                    ++ (" else " ++ genBlock d genTerm' a)
            BSwitch m cs def ->
                ("switch (" ++ snd (genOp' m) ++ ") {")
                    ++ precalate ("\n" ++ indent d) (map (genCase d genTerm') cs)
                    ++ ("\n" ++ indent d ++ "default: " ++ genBlock d genTerm' def)
                    ++ ("\n" ++ indent d ++ "}")
        genCase :: Int -> (Int -> term -> String) -> (Const, Block term) -> String
        genCase d genTerm' (c, blk) =
            "case "
                ++ fromRight (ice "uninit case") (snd (genConst c))
                ++ ": "
                ++ genBlock d genTerm' blk
                ++ " break;"
        genLoop :: Int -> (Int -> a -> String) -> Loop a -> String
        genLoop d genTerm' (Loop args body) =
            intercalate ("\n" ++ indent d) (map genLoopArg args)
                ++ ("\n" ++ indent d)
                ++ "while (true) "
                ++ genBlock d (genLoopTerm (map fst args) genTerm') body
        genLoopArg (Local x t, rhs) = genType t (lname' x) ++ case snd (genOp rhs) of
            Left _ -> ";" -- uninit
            Right v -> " = " ++ v ++ ";"
        genLoopTerm :: [Local] -> (Int -> term -> String) -> Int -> LoopTerminator term -> String
        genLoopTerm params genTerm' d = \case
            Continue args ->
                intercalate
                        ("\n" ++ indent d)
                        (catMaybes $ zipWith
                            (\param ->
                                either
                                        (const Nothing)
                                        (\arg -> Just (snd (genLocal param) ++ " = " ++ arg ++ ";")
                                        )
                                    . snd
                                    . genOp
                            )
                            params
                            args
                        )
                    ++ ("\n" ++ indent d ++ "continue;")
            Break a ->
                let s = genTerm' d a
                in  if "return " `isPrefixOf` s || "return;" `isPrefixOf` s
                        then s
                        else s ++ "\n" ++ indent d ++ "break;"
            LBranch br -> genBranch d (genLoopTerm params genTerm') br
        genExpr d genTerm' (Expr e _t) = case e of
            Call f as -> genTerm' . snd $ binop_call (genOp' f) (map (snd . genOp') as)
            Load addr -> genTerm' . snd $ preop "*" (genOp' addr)
            Mul a b -> binop' "*" a b
            Div a b -> binop' "/" a b
            Rem a b -> binop' "%" a b
            Add a b -> binop' "+" a b
            Sub a b -> binop' "-" a b
            Shl a b -> binop' "<<" a b
            LShr a b -> binop' ">>" a b -- FIXME: cast params to ensure logical shift or something?
            AShr a b -> binop' ">>" a b -- FIXME: cast params to ensure arithmetic shift or something?
            Gt a b -> binop' ">" a b
            GtEq a b -> binop' ">=" a b
            Lt a b -> binop' "<" a b
            LtEq a b -> binop' "<=" a b
            Eq a b -> binop' "==" a b
            Ne a b -> binop' "!=" a b
            BAnd a b -> binop' "&" a b
            BXor a b -> binop' "^" a b
            BOr a b -> binop' "|" a b

            EOperand op -> genTerm' (snd (genOp' op))
            ELoop loop -> genLoop d (flip genExpr genTerm') loop
            EGetMember i struct ->
                genTerm' . snd $ preop "&" (binop_access "->" (genOp' struct) (genMember i))
            EAsVariant x vi ->
                let
                    tid = asTConst (pointee (typeof x))
                    member = case tdefs Vec.!? fromIntegral tid of
                        Just (_, DUnion Union { unionVariants = vs }) -> fst $ fromMaybe
                            (ice
                            $ ("Variant Index " ++ show vi)
                            ++ (" out of range, n variants = " ++ show (Vec.length vs))
                            )
                            (vs Vec.!? fromIntegral vi)
                        Just tdef -> ice $ "EAsVariant of non pointer to union " ++ show tdef
                        Nothing -> ice
                            ("Type ID " ++ show tid ++ " out of range, n tdefs = " ++ show
                                (Vec.length tdefs)
                            )
                in
                    genTerm' . snd $ preop "&" (binop_access "->" (genOp' x) member)
            EBranch br -> genBranch d (flip genExpr genTerm') br
            Cast x t -> genTerm' . snd $ preop_cast (genType t "") (genOp' x)
            Bitcast x t -> genTerm' . snd $ preop_cast (genType t "") (genOp' x)
            where binop' op a b = genTerm' . snd $ binop op (genOp' a) (genOp' b)
        genOp' = second (either id id) . genOp
        -- Returns "precedence" of the operand, and the operand as a string. The string is in a
        -- Left if the operand is uninitialized.
        genOp :: Operand -> (Int, Either String String)
        genOp = \case
            OLocal l -> second Right (genLocal l)
            OGlobal g -> second Right (genGlobal g)
            OConst c -> genConst c
            OExtern (Extern x _ _ _) -> (0, Right x)
        genLocal (Local x _) =
            let x' = (0, lname lnames x) in if localIsAlloc x then preop "&" x' else x'

    defineMain =
        let (Global mainId _) = main
            main' = gname mainId
        in  unlines
                [ "int main(void) {"
                , "    install_stackoverflow_handler();"
                , "    carth_init();"
                , "    ((void(*)(void*))" ++ main' ++ ".m0.m1)(" ++ main' ++ ".m0.m0);"
                , "    return 0;"
                , "}"
                ]

    genConst' = second (either id id) . genConst
    -- Returns "precedence" and either Left on uninitialized (with a zero-value bundled, for when
    -- you can't leave things empty) or Right for defined value.
    genConst = \case
        Undef t -> (0, Left (genZero t))
        CInt { intVal = n, intWidth = w } -> (0, Right (genInt n w))
        CNat { natVal = n, natWidth = w } -> (0, Right (genNat n w))
        F32 x -> (0, Right (show x ++ "f"))
        F64 x -> (0, Right (show x))
        EnumVal { enumVariant = v } -> (0, Right v)
        Array t xs ->
            ( 0
            , Right $ printf "{%s}"
                             (genType (TArray t (fromIntegral (length xs))) "")
                             (intercalate ", " $ map (snd . genConst') xs)
            )
        CharArray cs -> (0, Right $ "\"" ++ decodeCharArrayStrLit (printf "\\x%02X") cs ++ "\"")
        Zero t -> (0, Right (genZero t))
        CBitcast x t -> second Right $ preop_cast (genType t "") (genConst' x)
        CGlobal g -> second Right $ genGlobal g
        CStruct _t ms -> (0, Right $ "{" ++ intercalate ", " (map (snd . genConst') ms) ++ " }")
        CPtrIndex p i -> second Right $ binop "+" (genConst' p) (0, show i)
    genInt n w = printf "INT%d_C(%d)" (ceilIntWidth w) n
    genNat n w = printf "UINT%d_C(%d)" (ceilIntWidth w) n
    genZero = \case
        TInt w -> genInt (0 :: Int) w
        TNat w -> genNat (0 :: Word) w
        TF32 -> "0.0f"
        TF64 -> "0.0"
        TPtr _ -> "NULL"
        VoidPtr -> "NULL"
        TFun{} -> "NULL"
        TConst _ -> "{0}"
        TArray _ _ -> "{0}"
        TClosure{} -> "{0}"

    preop op a =
        let prec = 2 -- All prefix operators in C have precedence 2
        in  (prec, op ++ precParen prec a)
    preop_cast t a = let prec = 2 in (prec, "(" ++ t ++ ")" ++ precParen prec a)
    binop op a b =
        let prec = case op of
                "*" -> 3
                "/" -> 3
                "%" -> 3
                "+" -> 4
                "-" -> 4
                "<<" -> 5
                ">>" -> 5
                ">" -> 6
                ">=" -> 6
                "<" -> 6
                "<=" -> 6
                "==" -> 7
                "!=" -> 7
                "&" -> 8
                "^" -> 9
                "|" -> 10
                _ -> ice $ "unexpected binary operator " ++ show op
        in  (prec, precParen prec a ++ " " ++ op ++ " " ++ precParen (prec - 1) b)
    binop_call f as = (1 :: Int, precParen 1 f ++ "(" ++ intercalate ", " as ++ ")")
    binop_access op source target =
        let prec = 1 -- Struct/union member access (through pointer) are both of precedence 1
        in  (prec, precParen prec source ++ op ++ target)
    precParen op_prec (a_prec, a_s) = if op_prec < a_prec then "(" ++ a_s ++ ")" else a_s

    genParam lnames p = genType (paramType p) (lname lnames (paramName p))
    lname lnames lid = fromMaybe
        (ice "Local ID " ++ show lid ++ " out of range, total len = " ++ show (Vec.length lnames))
        (lnames Vec.!? fromIntegral lid)

    genGlobal (Global x t) = case t of
        TFun{} -> (0, gname x)
        VoidPtr -> (0, gname x)
        _ -> preop "&" (0, gname x)
    gname gid = fromMaybe
        (ice $ "Global ID " ++ show gid ++ " out of range, total len = " ++ show
            (Vec.length gnames)
        )
        (gnames Vec.!? fromIntegral gid)

    genType = genType' tdefs

genType' :: Vector TypeDef -> Type -> String -> String
genType' tdefs t x = case t of
    TInt width -> "int" ++ show width ++ "_t" ++ pad x
    TNat width -> "uint" ++ show width ++ "_t" ++ pad x
    TF32 -> "float" ++ pad x
    TF64 -> "double" ++ pad x
    TPtr t -> genType' tdefs t $ case t of
        TArray _ _ -> "(*" ++ x ++ ")"
        _ -> "*" ++ x
    VoidPtr -> "void *" ++ x
    TFun outParam params ret ->
        maybe (genRet tdefs ret) (genType' tdefs . outParamType) outParam
            $ "(*"
            ++ x
            ++ ")("
            ++ intercalate ", " (map (genAnonParam tdefs) params)
            ++ ")"
    TConst ti -> typeName tdefs ti ++ pad x
    TArray t n -> genType' tdefs t (x ++ "[" ++ show n ++ "]")
    TClosure{} -> genType' tdefs (builtinType "closure") x
  where
    pad = \case
        "" -> ""
        x -> " " ++ x

genRet :: Vector TypeDef -> Ret -> String -> String
genRet tdefs = \case
    RetVal t -> genType' tdefs t
    RetVoid -> ("void " ++)

genAnonParam :: Vector TypeDef -> Param () -> String
genAnonParam tdefs p = genType' tdefs (paramType p) ""
