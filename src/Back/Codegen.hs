{-# LANGUAGE DuplicateRecordFields, GADTs, RankNTypes #-}

-- | Generation of LLVM IR code from our monomorphic AST.
module Back.Codegen (codegen) where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import LLVM.Prelude hiding (Const)
import LLVM.AST hiding (args, Type, Ret, Operand, Terminator, Switch, Add, Do, Store)
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
import qualified LLVM.AST.Constant as LL hiding (Add)
import Data.String
import System.FilePath
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Vector as Vec

import Misc
import Sizeof (variantsTagBits, variantsTagBytes)
import qualified Back.Low as Low
import Back.Low

data St = St
    { currentLabel :: Name
    , currentInstrs :: [Named LL.Instruction] -- In reverser order
    , labelCount :: Word
    , tmpCount :: Word
    }
type Gen = StateT St (Writer [BasicBlock])

codegen :: FilePath -> Program -> DataLayout -> ShortByteString -> Module
codegen moduleFilePath (Program funs exts gvars tdefs gnames) layout triple = Module
    { moduleName = fromString (takeBaseName moduleFilePath)
    , moduleSourceFileName = fromString moduleFilePath
    , moduleDataLayout = Just layout
    , moduleTargetTriple = Just triple
    , moduleDefinitions = concat
                              [ defineTypes
                              , declareExterns
                              , declareGlobals
                              -- TODO: init should be part of this already
                              , map defineFun funs
                              , [defineMain]
                              ]
    }
  where

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
    defineTypes :: [Definition]
    defineTypes = define =<< Vec.toList tdefs
      where
        define :: TypeDef -> [Definition]
        define = \case
            Enum _ _ -> []
            Struct name ms ->
                [TypeDefinition (mkName name) (Just (structType (map genType ms)))]
            Data' (Data name vs aMax sMax) ->
                let sTag = max (variantsTagBytes vs) aMax
                    tag = IntegerType (8 * fromIntegral sTag)
                    fill = ArrayType (fromIntegral (div (sMax + aMax - 1) aMax))
                                     (IntegerType (8 * fromIntegral aMax))
                in  [TypeDefinition (mkName name) (Just (structType [tag, fill]))]

    declareExterns :: [Definition]
    declareExterns = map declare exts
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

    declareGlobals :: [Definition]
    declareGlobals = map declare gvars
      where
        declare g =
            let (isconst, ident, initializer) = case g of
                    GVarDef (Global x t) _ _ -> (False, x, LL.Undef (genType t))
                    GConstDef (Global x _) c -> (True, x, genConst c)
            in  GlobalDefinition $ GlobalVariable { LLGlob.name = mkName (getGName ident)
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

    defineFun :: FunDef -> Definition
    defineFun (FunDef ident ps r block lnames) =
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
            simpleFun LL.Internal (getGName ident) ps' rt (genFunBody lnames block)

    -- TODO: In this incarnation, this outermost main should just call init and
    --       user-main. init will in turn init global vars & setup stack overflow handler etc.
    defineMain :: Definition
    defineMain = simpleFun LL.External "main" [] LL.i32 $ pure $ BasicBlock
        (mkName "entry")
        [ LL.Do (callNamed "install_stackoverflow_handler" [] LL.void)
        , LL.Do (callNamed "carth_init" [] LL.void)
        , LL.Do (callNamed "carth_main" [] LL.void)
        ]
        (LL.Do (LL.Ret (Just (ConstantOperand (LL.Int 32 0))) []))

    genFunBody :: VarNames -> Block Terminator -> [LL.BasicBlock]
    genFunBody lnames body = execWriter (evalStateT (genTBlock body) (St "entry" [] 0 0))
      where
        genEBranch :: Branch Expr -> Gen LL.Operand
        genEBranch = \case
            If p c a -> do
                lc <- label "CONSEQ"
                la <- label "ALTERN"
                commitThen (LL.CondBr (genLocal p) lc la []) lc
                econverge (genEBlock c) [(la, genEBlock a)]
            Switch _ _ _ -> _

        econverge :: Gen LL.Operand -> [(Name, Gen LL.Operand)] -> Gen LL.Operand
        econverge default' cases = _

        genTBranch :: Branch Terminator -> Gen ()
        genTBranch = \case
            If p c a -> do
                lc <- label "CONSEQ"
                la <- label "ALTERN"
                commitThen (LL.CondBr (genLocal p) lc la []) lc
                tconverge (genTBlock c) [(la, genTBlock a)]
            Switch _ _ _ -> _

        tconverge :: Gen () -> [(Name, Gen ())] -> Gen ()
        tconverge genDefault cases = do
            genDefault
            forM_ cases $ \(l, genCase) -> do
                modify (\st -> st { currentLabel = l })
                genCase

        genSBranch :: Branch () -> Gen ()
        genSBranch = \case
            If p c a -> do
                lc <- label "CONSEQ"
                la <- label "ALTERN"
                ln <- label "NEXT"
                commitThen (LL.CondBr (genLocal p) lc la []) lc
                sconverge (genSBlock c) [(la, genSBlock a)]
            Switch _ _ _ -> _

        sconverge :: Gen () -> [(Name, Gen ())] -> Gen ()
        sconverge genDefault cases = do
            ln <- label "NEXT"
            genDefault
            forM cases $ \(l, genCase) -> do
                commitThen (LL.Br ln []) l
                genCase
            commitThen (LL.Br ln []) ln

        genTBlock :: Block Terminator -> Gen ()
        genTBlock = \case
            Block [] term -> genTerm term
            Block (stm : stms) term -> genStm stm *> (genTBlock (Block stms term))

        genSBlock :: Block () -> Gen ()
        genSBlock = \case
            Block [] () -> pure ()
            Block (stm : stms) () -> genStm stm *> genSBlock (Block stms ())

        genStm :: Statement -> Gen ()
        genStm = \case
            Let lhs rhs -> _
            Store v dst -> store (genOperand v) (genOperand dst)
            Loop blk -> _
            SBranch br -> genSBranch br
            Do e -> genExpr e $> ()

        genTerm :: Terminator -> Gen ()
        genTerm = \case
            TRetVal x -> commitFinal (LL.Ret (Just (genOperand x)) [])
            TRetVoid -> commitFinal (LL.Ret Nothing [])
            TOutParam x ->
                let x' = genOperand x
                in  store x' (LocalReference (LL.ptr (LL.typeOf x')) (mkName "out"))
                        *> commitFinal (LL.Ret Nothing [])
            TBranch br -> genTBranch br

        store :: LL.Operand -> LL.Operand -> Gen ()
        store v dst = emitDo $ LL.Store { volatile = False
                                        , address = dst
                                        , value = v
                                        , maybeAtomicity = Nothing
                                        , alignment = 0
                                        , metadata = []
                                        }


        genEBlock :: Block Expr -> Gen LL.Operand
        genEBlock = \case
            Block [] e -> genExpr e
            Block (stm : stms) e -> genStm stm *> (genEBlock (Block stms e))

        -- TODO: More elegant code for nested branches. Collapse in a single, flat step,
        --       instead of level-wise.
        genExpr :: Expr -> Gen LL.Operand
        genExpr = \case
            Add a b ->
                let (a', b') = (genOperand a, genOperand b)
                in  emit (LL.typeOf a') (LL.Add False False a' b' [])
            EBranch br -> genEBranch br

        genOperand :: Operand -> LL.Operand
        genOperand = \case
            OLocal x -> genLocal x
            _ -> _

        genLocal :: Local -> LL.Operand
        genLocal (Local ident t) =
            LocalReference (genType t) (mkName (getName lnames ident))

        emit :: LL.Type -> LL.Instruction -> Gen LL.Operand
        emit t instr = do
            n <- gets tmpCount
            modify (\st -> st { tmpCount = n + 1 })
            let name = "tmp" ++ show n
            emitNamed name t instr

        emitNamed :: String -> LL.Type -> LL.Instruction -> Gen LL.Operand
        emitNamed x t instr = do
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
        TConst i -> case (tdefs Vec.! fromIntegral i) of
            Enum _ vs -> LL.IntegerType (variantsTagBits vs)
            Struct x _ -> LL.NamedTypeReference (mkName x)
            Data' (Data x _ _ _) -> LL.NamedTypeReference (mkName x)
      where
        genParam = \case
            ByVal () pt -> genType pt
            ByRef () pt -> LL.ptr (genType pt)

    getGName = getName gnames

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
