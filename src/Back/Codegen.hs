{-# LANGUAGE DuplicateRecordFields, GADTs, RankNTypes, ScopedTypeVariables #-}

-- | Generation of LLVM IR code from our monomorphic AST.
module Back.Codegen (codegen) where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import LLVM.Prelude hiding (Const)
import LLVM.AST (Name (..), Named, BasicBlock (..), Module (..), Definition (..), Global (..), Type (..), Instruction, Parameter (..), mkName, Operand (ConstantOperand))
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
import qualified LLVM.AST.Constant as LL (Constant (Undef, Float, Array, Null, AggregateZero, Int, GlobalReference))
import qualified LLVM.AST.Constant as LLConst
import qualified LLVM.AST.IntegerPredicate as LLIPred
import qualified LLVM.AST.FloatingPointPredicate as LLFPred
import Data.Either
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.String
import System.FilePath
import qualified Data.Vector as Vec

import Misc
import Sizeof (variantsTagBits, toBits)
import Back.Low as Low

data St = St
    { currentLabel :: Name
    , currentInstrs :: [Named LL.Instruction] -- In reverser order
    , labelCount :: Word
    , tmpCount :: Word
    , aliases :: Map String LL.Operand
    }
type Gen = StateT St (Writer [BasicBlock])

data GExpr = GInstr LL.Type LL.Instruction | GOperand LL.Operand

codegen :: DataLayout -> ShortByteString -> Bool -> FilePath -> Program -> Module
codegen layout triple noGC' moduleFilePath (Program funs exts gvars tdefs gnames main) =
    Module
        { moduleName = fromString (takeBaseName moduleFilePath)
        , moduleSourceFileName = fromString moduleFilePath
        , moduleDataLayout = Just layout
        , moduleTargetTriple = Just triple
        , moduleDefinitions = concat
                                  [ defineTypes
                                  , defineBuiltinsHidden
                                  , declareExterns
                                  , declareGlobals
                                  , map defineFun funs
                                  , [defineMain]
                                  ]
        }
  where

    defineTypes :: [Definition]
    defineTypes = define =<< Vec.toList tdefs
      where
        define :: TypeDef -> [Definition]
        define (name, d) = case d of
            DEnum _ -> []
            DStruct s -> pure $ TypeDefinition
                (mkName name)
                (Just (structType (map genType (structMembers s))))
            DUnion Union { unionGreatestSize = sMax, unionGreatestAlignment = aMax } ->
                let fill = ArrayType (fromIntegral (div (sMax + aMax - 1) aMax))
                                     (IntegerType (fromIntegral (toBits aMax)))
                -- In LLVM, only structs can be identified type definitions, so wrap
                -- the array in a singleton struct, since we want to see the type name
                -- in generated code.
                in  [TypeDefinition (mkName name) (Just (structType [fill]))]

    defineBuiltinsHidden :: [Definition]
    defineBuiltinsHidden = map declare (Map.toList builtinsHidden)
      where
        declare (x, (ps, tr)) = simpleFun LL.External x ps tr []

        builtinsHidden :: Map String ([Parameter], LL.Type)
        builtinsHidden = Map.fromList [("install_stackoverflow_handler", ([], LL.void))]

    declareExterns :: [Definition]
    declareExterns = map declare exts
      where
        declare (ExternDecl name out ps r) =
            let anon = mkName ""
                rt = case r of
                    RetVal t -> genType t
                    RetVoid -> LL.void
                out' = case out of
                    Nothing -> []
                    Just (OutParam _ t) ->
                        [Parameter (LL.ptr (genType t)) anon [LL.SRet]]
                ps' = flip map ps $ \case
                    ByVal () t -> Parameter (genType t) anon []
                    ByRef () t -> Parameter (LL.ptr (genType t)) anon []
            in  simpleFun LL.External name (out' ++ ps') rt []

    declareGlobals :: [Definition]
    declareGlobals = map declare gvars
      where
        declare g =
            let (isconst, ident, t, initializer) = case g of
                    GlobVarDecl x t -> (False, x, genType t, LL.Undef (genType t))
                    GlobConstDef x t c -> (True, x, genType t, genConst c)
            in  GlobalDefinition $ GlobalVariable { LLGlob.name = mkName (getGName ident)
                                                  , LLGlob.linkage = LL.Private
                                                  , LLGlob.visibility = LLVis.Default
                                                  , LLGlob.dllStorageClass = Nothing
                                                  , LLGlob.threadLocalMode = Nothing
                                                  , LLGlob.addrSpace = LLAddr.AddrSpace 0
                                                  , LLGlob.unnamedAddr = Nothing
                                                  , LLGlob.isConstant = isconst
                                                  , LLGlob.type' = t
                                                  , LLGlob.initializer = Just initializer
                                                  , LLGlob.section = Nothing
                                                  , LLGlob.comdat = Nothing
                                                  , LLGlob.alignment = 0
                                                  , LLGlob.metadata = []
                                                  }

    genConst :: Const -> LL.Constant
    genConst = \case
        Undef t -> LL.Undef (genType t)
        CInt { intWidth = w, intVal = v } -> LL.Int (fromIntegral w) v
        CNat { natWidth = w, natVal = v } -> LL.Int (fromIntegral w) (fromIntegral v)
        F32 x -> LL.Float (LL.Single x)
        F64 x -> LL.Float (LL.Double x)
        -- In the LLVM backend, we elide all enum name information, leaving just the
        -- integer value
        EnumVal { enumWidth = w, enumVal = v } ->
            LL.Int (fromIntegral w) (fromIntegral v)
        Array t xs -> LL.Array (genType t) (map genConst xs)
        CharArray cs -> LL.Array LL.i8 (map (LL.Int 8 . fromIntegral) cs)
        Zero t -> case genType t of
            t'@(LL.PointerType _ _) -> LL.Null t'
            t' -> LL.AggregateZero t'
        CBitcast x t -> LLConst.BitCast (genConst x) (genType t)
        CGlobal (Global x t) -> LL.GlobalReference (genType t) (mkName (getGName x))
        CStruct t ms -> LLConst.Struct
            (case genType t of
                LL.NamedTypeReference tname -> Just tname
                _ -> Nothing
            )
            False
            (map genConst ms)
        CPtrIndex p i ->
            LLConst.GetElementPtr False (genConst p) [LL.Int 64 (fromIntegral i)]

    defineFun :: FunDef -> Definition
    defineFun (FunDef ident out ps r block allocs lnames) =
        let rt = case r of
                RetVal t -> genType t
                RetVoid -> LL.void
            out' = case out of
                Nothing -> []
                Just (OutParam x t) ->
                    [Parameter (LL.ptr (genType t)) (mkName (getName lnames x)) [LL.SRet]]
            ps' = flip map ps $ \case
                ByVal x t -> Parameter (genType t) (mkName (getName lnames x)) []
                ByRef x t ->
                    Parameter (LL.ptr (genType t)) (mkName (getName lnames x)) []
        in  simpleFun LL.Internal
                      (getGName ident)
                      (out' ++ ps')
                      rt
                      (genFunBody lnames allocs block)

    -- In this incarnation, this outermost main should just call init and
    -- user-main. init will in turn init global vars & setup stack overflow handler etc.
    defineMain :: Definition
    defineMain = simpleFun LL.External "main" [] LL.i32 $ pure $ BasicBlock
        (mkName "entry")
        [ LL.Do (callNamed "install_stackoverflow_handler" Nothing [] LL.void)
        , LL.Do (callNamed "carth_init" Nothing [] LL.void)
        , mkName "mainc_tmp" LL.:= LL.GetElementPtr
            { inBounds = False
            , address = LL.ConstantOperand (genGlobal main)
            , indices = [litI64 (0 :: Word), litI32 (0 :: Word), litI32 (0 :: Word)]
            , metadata = []
            }
        , mkName "mainc" LL.:= LL.Load
            { volatile = False
            , address = LL.LocalReference (LL.ptr (LL.ptr LL.i8)) (mkName "mainc_tmp")
            , maybeAtomicity = Nothing
            , alignment = 0
            , metadata = []
            }
        , mkName "mainf_tmp" LL.:= LL.GetElementPtr
            { inBounds = False
            , address = LL.ConstantOperand (genGlobal main)
            , indices = [litI64 (0 :: Word), litI32 (0 :: Word), litI32 (1 :: Word)]
            , metadata = []
            }
        , mkName "mainf_tmp2" LL.:= LL.Load
            { volatile = False
            , address = LL.LocalReference (LL.ptr (LL.ptr LL.i8)) (mkName "mainf_tmp")
            , maybeAtomicity = Nothing
            , alignment = 0
            , metadata = []
            }
        , mkName "mainf"
            LL.:= LL.BitCast (LL.LocalReference (LL.ptr LL.i8) (mkName "mainf_tmp2"))
                             (LL.ptr (FunctionType LL.void [LL.ptr LL.i8] False))
                             []
        , LL.Do
            (call
                (LL.LocalReference
                    (LL.ptr (FunctionType LL.void [LL.ptr LL.i8] False))
                    (mkName "mainf")
                )
                Nothing
                [LL.LocalReference (LL.ptr LL.i8) (mkName "mainc")]
            )
        ]
        (LL.Do (LL.Ret (Just (ConstantOperand (LL.Int 32 0))) []))

    genFunBody :: VarNames -> Allocs -> Block Terminator -> [LL.BasicBlock]
    genFunBody lnames allocs body = execWriter
        (evalStateT (genAllocs allocs *> genBlock genTerminator body) initSt)
      where
        initSt = St { currentLabel = "entry"
                    , currentInstrs = []
                    , labelCount = 0
                    , tmpCount = 0
                    , aliases = Map.empty
                    }

        genAllocs = mapM_ $ \(x, t) ->
            let t' = genType t
            in  emitNamed (getName lnames x)
                          (GInstr (LL.ptr t') (LL.Alloca t' Nothing 0 []))
                    $> ()

        genEBranch :: Branch Expr -> Gen GExpr
        genEBranch = \case
            BIf p c a -> genIf p c a genExpr econverge
            BSwitch x cs d -> genSwitch x cs d genExpr econverge

        econverge :: Gen GExpr -> [(Name, Gen GExpr)] -> Gen GExpr
        econverge genDefault cases = do
            ln <- label "NEXT"
            d <- emit =<< genDefault
            ld <- gets currentLabel
            cs <- forM cases $ \(l, genCase) -> do
                commitThen (LL.Br ln []) l
                c <- emit =<< genCase
                lc <- gets currentLabel
                pure (c, lc)
            commitThen (LL.Br ln []) ln
            let t = LL.typeOf d
            pure (GInstr t (LL.Phi t ((d, ld) : cs) []))

        genSBranch :: Branch () -> Gen ()
        genSBranch = \case
            BIf p c a -> genIf p c a pure sconverge
            BSwitch x cs d -> genSwitch x cs d pure sconverge

        sconverge :: Gen () -> [(Name, Gen ())] -> Gen ()
        sconverge genDefault cases = do
            ln <- label "NEXT"
            genDefault
            forM_ cases $ \(l, genCase) -> do
                commitThen (LL.Br ln []) l
                genCase
            commitThen (LL.Br ln []) ln

        genBlock :: (term -> Gen out) -> Block term -> Gen out
        genBlock genTerm (Block stms term) = forM_ stms genStm *> genTerm term

        genIf
            :: Low.Operand
            -> Block t
            -> Block t
            -> (t -> Gen a)
            -> (Gen a -> [(Name, Gen a)] -> Gen b)
            -> Gen b
        genIf p c a genTerm converge = do
            lc <- label "CONSEQ"
            la <- label "ALTERN"
            p' <- genOperand p
            p'' <- emit $ GInstr LL.i1 (LL.Trunc p' LL.i1 [])
            commitThen (LL.CondBr p'' lc la []) lc
            converge (genBlock genTerm c) [(la, genBlock genTerm a)]

        genSwitch
            :: Low.Operand
            -> [(Const, Block t)]
            -> Block t
            -> (t -> Gen a)
            -> (Gen a -> [(Name, Gen a)] -> Gen a)
            -> Gen a
        genSwitch x cs d genTerm converge = do
            ld <- label "DEFAULT"
            lcs <- mapM (const (label "CASE")) cs
            x' <- genOperand x
            commitThen (LL.Switch x' ld (zip (map (genConst . fst) cs) lcs) []) ld
            converge (genBlock genTerm d) (zip lcs (map (genBlock genTerm . snd) cs))

        genStm :: Statement -> Gen ()
        genStm = \case
            Let lhs rhs -> genExpr rhs >>= \rhs' -> emitLocal lhs rhs' $> ()
            Store v dst -> bindM2 store (genOperand v) (genOperand dst)
            SBranch br -> genSBranch br
            VoidCall f out as -> emitDo =<< liftM3 call
                                                   (genOperand f)
                                                   (mapM genOperand out)
                                                   (mapM genOperand as)
            SLoop loop -> genLoop loop pure (const (pure ()))

        genTerminator :: Terminator -> Gen ()
        genTerminator = \case
            TRetVal x -> genExpr x >>= emit >>= \v -> commitFinal (LL.Ret (Just v) [])
            TRetVoid -> commitFinal (LL.Ret Nothing [])

        store :: LL.Operand -> LL.Operand -> Gen ()
        store v dst = emitDo $ LL.Store { volatile = False
                                        , address = dst
                                        , value = v
                                        , maybeAtomicity = Nothing
                                        , alignment = 0
                                        , metadata = []
                                        }

        -- TODO: More elegant code for nested branches. Collapse in a single, flat step,
        --       instead of level-wise.
        genExpr :: Expr -> Gen GExpr
        genExpr (Expr e t) = do
            let t' = genType t
            let arith uop sop fop a b = do
                    (a', b') <- liftM2 (,) (genOperand a) (genOperand b)
                    let op = if
                            | isFloat t -> fop
                            | isInt t -> sop
                            | otherwise -> uop
                    pure (GInstr t' (op a' b' []))
                logic op a b = do
                    (a', b') <- liftM2 (,) (genOperand a) (genOperand b)
                    pure (GInstr t' (op a' b' []))
                rel uop sop fop a b = do
                    (a', b') <- liftM2 (,) (genOperand a) (genOperand b)
                    let op = if
                            | isFloat (typeof a) -> LL.FCmp fop
                            | isInt (typeof a) -> LL.ICmp sop
                            | otherwise -> LL.ICmp uop
                    r <- emit $ GInstr LL.i1 (op a' b' [])
                    pure (GInstr LL.i8 (LL.ZExt r LL.i8 []))
            case e of
                Add a b -> arith (LL.Add False False)
                                 (LL.Add False False)
                                 (LL.FAdd LL.noFastMathFlags)
                                 a
                                 b
                Sub a b -> arith (LL.Sub False False)
                                 (LL.Sub False False)
                                 (LL.FSub LL.noFastMathFlags)
                                 a
                                 b
                Mul a b -> arith (LL.Mul False False)
                                 (LL.Mul False False)
                                 (LL.FMul LL.noFastMathFlags)
                                 a
                                 b
                Div a b -> arith (LL.UDiv False)
                                 (LL.SDiv False)
                                 (LL.FDiv LL.noFastMathFlags)
                                 a
                                 b
                Rem a b -> arith LL.URem LL.SRem (LL.FRem LL.noFastMathFlags) a b
                Shl a b -> logic (LL.Shl False False) a b
                LShr a b -> logic (LL.LShr False) a b
                AShr a b -> logic (LL.AShr False) a b
                BAnd a b -> logic LL.And a b
                BOr a b -> logic LL.Or a b
                BXor a b -> logic LL.Xor a b
                Eq a b -> rel LLIPred.EQ LLIPred.EQ LLFPred.OEQ a b
                Ne a b -> rel LLIPred.NE LLIPred.NE LLFPred.ONE a b
                Gt a b -> rel LLIPred.UGT LLIPred.SGT LLFPred.OGT a b
                GtEq a b -> rel LLIPred.UGE LLIPred.SGE LLFPred.OGE a b
                Lt a b -> rel LLIPred.ULT LLIPred.SLT LLFPred.OLT a b
                LtEq a b -> rel LLIPred.ULE LLIPred.SLE LLFPred.OLE a b
                Load src -> do
                    src' <- genOperand src
                    pure $ GInstr
                        t'
                        LL.Load { volatile = False
                                , address = src'
                                , maybeAtomicity = Nothing
                                , alignment = 0
                                , metadata = []
                                }
                Call f as -> liftM3 (GInstr t' .** call)
                                    (genOperand f)
                                    (pure Nothing)
                                    (mapM genOperand as)
                EBranch br -> genEBranch br
                EGetMember i x -> genOperand x <&> \x' -> GInstr
                    t'
                    LL.GetElementPtr { inBounds = False
                                     , address = x'
                                     , indices = [litI64 (0 :: Integer), litI32 i]
                                     , metadata = []
                                     }
                EAsVariant x _ ->
                    genOperand x <&> \x' -> GInstr t' (LL.BitCast x' (genType t) [])
                EOperand x -> GOperand <$> genOperand x
                ELoop loop -> genLoop loop (emit <=< genExpr) $ \breaks -> do
                    let t = LL.typeOf . fst . head $ breaks
                    pure $ GInstr t (LL.Phi t breaks [])
                Cast x t -> do
                    let tx = typeof x
                    x' <- genOperand x
                    let t' = genType t
                    pure $ case (tx, t) of
                        _
                            | tx == t
                            -> GOperand x'
                            | Just w1 <- integralWidth tx
                            , Just w2 <- integralWidth t
                            , w1 == w2
                            -> GOperand x'
                        (_, TInt w2) | Just w1 <- integralWidth tx ->
                            GInstr t' $ if w2 < w1
                                then LL.Trunc x' t' []
                                else LL.SExt x' t' []
                        (_, TNat w2) | Just w1 <- integralWidth tx ->
                            GInstr t' $ if w2 < w1
                                then LL.Trunc x' t' []
                                else LL.ZExt x' t' []
                        (TF32, TF64) -> GInstr t' (LL.FPExt x' t' [])
                        (TF64, TF32) -> GInstr t' (LL.FPTrunc x' t' [])
                        (TInt _, _) | isFloat t -> GInstr t' (LL.SIToFP x' t' [])
                        (TNat _, _) | isFloat t -> GInstr t' (LL.UIToFP x' t' [])
                        (_, TInt _) | isFloat tx -> GInstr t' (LL.FPToSI x' t' [])
                        (_, TNat _) | isFloat tx -> GInstr t' (LL.FPToUI x' t' [])
                        _ -> ice $ "genExpr.Cast: " ++ show tx ++ " to " ++ show t
                Bitcast x t -> do
                    x' <- genOperand x
                    let t' = genType t
                    pure (GInstr t' (LL.BitCast x' t' []))

        genLoop
            :: forall t a b . Loop t -> (t -> Gen a) -> ([(a, Name)] -> Gen b) -> Gen b
        genLoop (Loop params (Block stms term)) genTerm joinBreaks = do
            ll <- label "LOOP_BODY"
            la <- label "LOOP_ASSIGN"
            le <- label "LOOP_END"
            lprev <- gets currentLabel
            commitThen (LL.Br la []) ll
            let genLTerm
                    :: LoopTerminator t -> Gen [Either ([LL.Operand], Name) (a, Name)]
                genLTerm = \case
                    Continue args -> do
                        l <- gets currentLabel
                        commitThen (LL.Br la []) la
                        args' <- mapM genOperand args
                        pure [Left (args', l)]
                    Break x -> do
                        l <- gets currentLabel
                        x' <- genTerm x
                        commitThen (LL.Br le []) la
                        pure [Right (x', l)]
                    LBranch br -> genLBranch br

                genLBranch = \case
                    BIf p c a -> genIf p c a genLTerm lconverge
                    BSwitch x cs d -> genSwitch x cs d genLTerm lconverge

                lconverge
                    :: Gen [Either ([LL.Operand], Name) (a, Name)]
                    -> [(Name, Gen [Either ([LL.Operand], Name) (a, Name)])]
                    -> Gen [Either ([LL.Operand], Name) (a, Name)]
                lconverge genDefault cases = do
                    d <- genDefault
                    cs <- forM cases $ \(l, genCase) -> do
                        modify (\st -> st { currentLabel = l })
                        genCase
                    pure (concat (d : cs))

            -- In LOOP
            forM_ stms genStm
            (conts, breaks) <- partitionEithers <$> genLTerm term
            -- In ASSIGN
            let conts' = transpose
                    (map (\(nexts, lnext) -> zip nexts (repeat lnext)) conts)
            forM_ (zip params conts') $ \((lhs, init), nexts) -> do
                init' <- genOperand init
                let u = LL.typeOf init'
                emitLocal lhs (GInstr u (LL.Phi u ((init', lprev) : nexts) []))
            commitThen (LL.Br ll []) le
            -- In END
            joinBreaks breaks

        genOperand :: Low.Operand -> Gen LL.Operand
        genOperand = \case
            OLocal x -> genLocal x
            OGlobal x -> pure $ LL.ConstantOperand (genGlobal x)
            OConst c -> pure $ LL.ConstantOperand (genConst c)
            OExtern e -> pure $ LL.ConstantOperand (genExtern e)

        genLocal :: Local -> Gen LL.Operand
        genLocal (Local ident t) =
            let name = getName lnames ident
            in  gets aliases <&> Map.lookup name <&> \case
                    Just x -> x
                    Nothing -> LL.LocalReference (genType t) (mkName name)

        genExtern :: Low.Extern -> LL.Constant
        genExtern (Extern name out params ret) =
            LL.GlobalReference (genType (TFun out params ret)) (mkName name)

        emit :: GExpr -> Gen LL.Operand
        emit (GOperand x) = pure x
        emit e = do
            n <- gets tmpCount
            modify (\st -> st { tmpCount = n + 1 })
            let name = "tmp" ++ show n
            emitNamed name e

        emitLocal :: Local -> GExpr -> Gen LL.Operand
        emitLocal (Local x _) = emitNamed (getName lnames x)

        emitNamed :: String -> GExpr -> Gen LL.Operand
        emitNamed lhs (GOperand rhs) =
            modify (\st -> st { aliases = Map.insert lhs rhs (aliases st) }) $> rhs
        emitNamed x (GInstr t instr) = do
            let instr' = mkName x LL.:= instr
            modify (\st -> st { currentInstrs = instr' : currentInstrs st })
            pure (LL.LocalReference t (mkName x))

        emitDo :: LL.Instruction -> Gen ()
        emitDo instr =
            modify (\st -> st { currentInstrs = LL.Do instr : currentInstrs st })

        label :: String -> Gen Name
        label s = do
            n <- gets labelCount
            modify (\st -> st { labelCount = n + 1 })
            pure $ mkName ("L" ++ show n ++ s)

    genGlobal :: Low.Global -> LL.Constant
    genGlobal (Global ident t) = LL.GlobalReference (genType t) (mkName (getGName ident))

    genType :: Low.Type -> LL.Type
    genType = \case
        TInt { tintWidth = w } -> LL.IntegerType (fromIntegral w)
        TNat { tnatWidth = w } -> LL.IntegerType (fromIntegral w)
        TF32 -> LL.FloatingPointType LL.FloatFP
        TF64 -> LL.FloatingPointType LL.DoubleFP
        TPtr u -> LL.ptr (genType u)
        VoidPtr -> LL.ptr LL.i8
        TFun out ps r ->
            let rt = case r of
                    RetVal t -> genType t
                    RetVoid -> LL.void
                out' = maybe [] ((: []) . genOutParam) out
            in  LL.ptr $ LL.FunctionType rt (out' ++ map genParam ps) False
        TConst i -> case tdefs Vec.! fromIntegral i of
            (_, DEnum vs) -> LL.IntegerType (variantsTagBits vs)
            (name, _) -> LL.NamedTypeReference (mkName name)
        TArray t n -> LL.ArrayType (fromIntegral n) (genType t)
        TClosure{} -> LL.NamedTypeReference (mkName "closure")
      where
        genOutParam (OutParam () pt) = LL.ptr (genType pt)
        genParam = \case
            ByVal () pt -> genType pt
            ByRef () pt -> LL.ptr (genType pt)

    getGName = getName $ if noGC'
        then flip Vec.map gnames $ \case
            "GC_malloc" -> "malloc"
            s -> s
        else gnames

    litI64 :: Integral a => a -> LL.Operand
    litI64 = LL.ConstantOperand . LL.Int 64 . toInteger

    litI32 :: Integral a => a -> LL.Operand
    litI32 = LL.ConstantOperand . LL.Int 32 . toInteger

commitThen :: LL.Terminator -> Name -> Gen ()
commitThen term next = do
    current <- gets currentLabel
    rinstrs <- gets currentInstrs
    let instrs = reverse rinstrs
    tell [BasicBlock current instrs (LL.Do term)]
    modify (\st -> st { currentLabel = next, currentInstrs = [] })

commitFinal :: LL.Terminator -> Gen ()
commitFinal term = commitThen term (ice "Continued codegen after commitFinal")

getName :: VarNames -> Word -> String
getName names i = names Vec.! fromIntegral i

structType :: [LL.Type] -> LL.Type
structType ts = StructureType { isPacked = False, elementTypes = ts }

callNamed :: String -> Maybe LL.Operand -> [LL.Operand] -> LL.Type -> Instruction
callNamed f out as rt =
    let f' = ConstantOperand $ LL.GlobalReference
            (LL.ptr $ FunctionType rt
                                   (maybe id ((:) . LL.typeOf) out $ map LL.typeOf as)
                                   False
            )
            (mkName f)
    in  call f' out as

call :: LL.Operand -> Maybe LL.Operand -> [LL.Operand] -> Instruction
call f out as = LL.Call
    { tailCallKind = Just LL.NoTail
    , callingConvention = LL.C
    , returnAttributes = []
    , function = Right f
    , arguments = maybe [] ((: []) . (, [LL.SRet])) out ++ map (, []) as
    , functionAttributes = []
    , metadata = []
    }

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
