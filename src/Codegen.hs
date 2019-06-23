{-# LANGUAGE OverloadedStrings, LambdaCase, TemplateHaskell, TupleSections
  , FlexibleContexts #-}

module Codegen (codegen) where

import LLVM.Prelude (ShortByteString)
import LLVM.AST
import LLVM.AST.Typed
import LLVM.AST.Type hiding (ptr)
import qualified LLVM.AST.Type as LLType
import qualified LLVM.AST.CallingConvention as LLCallConv
import qualified LLVM.AST.Linkage as LLLink
import qualified LLVM.AST.Visibility as LLVis
import qualified LLVM.AST.Constant as LLConst
import qualified LLVM.AST.Float as LLFloat
import qualified LLVM.AST.Global as LLGlob
import qualified LLVM.AST.AddrSpace as LLAddr
import qualified Data.Text.Prettyprint.Doc as Prettyprint
import qualified Codec.Binary.UTF8.String as UTF8.String
import LLVM.Pretty ()
import Data.String
import System.FilePath
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Char
import Data.Bool
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Word
import Data.Foldable
import Control.Applicative
import Control.Lens
    (makeLenses, modifying, scribe, (<<+=), use, uses, assign, views, locally)

import Misc
import Ast (TPrim(..))
import qualified Annot as An
import qualified Mono

-- | An instruction that returns a value. The name refers to the fact that a
-- mathematical function always returns a value, but an imperative procedure may
-- only produce side effects.
data FunInstruction = WithRetType Instruction Type

-- TODO: Either treat globals and locals separately - Globals behing pointers, locals not - or treat them the same - stack alloc space for locals.
data Env = Env
    { _localEnv :: Map Mono.MTypedVar Operand
    , _globalEnv :: Map Mono.MTypedVar Operand
    }
makeLenses ''Env

data St = St
    { _currentBlockLabel :: Name
    , _currentBlockInstrs :: [Named Instruction]
    , _registerCount :: Word
    }
makeLenses ''St

type Gen' = StateT St (Reader Env)

-- | The output of generating a function
data Out = Out
    { _outBlocks :: [BasicBlock]
    , _outStrings :: [(Name, String)]
    , _outFuncs :: [(Name, [Mono.MTypedVar], (String, Mono.Type), Mono.MExpr)]}
makeLenses ''Out

instance Semigroup Out where
    Out bs1 ss1 fs1 <> Out bs2 ss2 fs2 =
        Out (bs1 <> bs2) (ss1 <> ss2) (fs1 <> fs2)

instance Monoid Out where
    mempty = Out [] [] []

type Gen = WriterT Out Gen'

callConv :: LLCallConv.CallingConvention
callConv = LLCallConv.C

runGen' :: Gen' a -> a
runGen' g = runReader (evalStateT g initSt) initEnv

semiExecRetGen :: Gen Operand -> Gen' (Type, Out)
semiExecRetGen gx = runWriterT $ do
    x <- gx
    commitFinalFuncBlock (ret x)
    pure (typeOf x)

initEnv :: Env
initEnv = Env {_localEnv = Map.empty, _globalEnv = Map.empty}

initSt :: St
initSt = St
    { _currentBlockLabel = "entry"
    , _currentBlockInstrs = []
    , _registerCount = 0
    }


codegen :: FilePath -> Mono.MProgram -> Module
codegen moduleFilePath (An.Program main (Mono.Defs defs)) =
    let
        defs' = (Mono.TypedVar "main" Mono.mainType, main) : Map.toList defs
        genGlobDefs = withGlobDefSigs
            defs'
            (liftA2 (:) genOuterMain (fmap join (mapM genGlobDef defs')))
    in defaultModule
        { moduleName = fromString ((takeBaseName moduleFilePath))
        , moduleSourceFileName = fromString moduleFilePath
        , moduleDefinitions = genBuiltins ++ runGen' genGlobDefs
        }

genBuiltins :: [Definition]
genBuiltins = map
    (GlobalDefinition . ($ []))
    [ simpleFunc
        (mkName "malloc")
        [parameter (mkName "size") i64]
        (LLType.ptr typeUnit)
    , simpleFunc (mkName "printInt") [parameter (mkName "n") i64] typeUnit
    ]

genOuterMain :: Gen' Definition
genOuterMain = do
    assign currentBlockLabel (mkName "entry")
    assign currentBlockInstrs []
    (_, Out basicBlocks _ _) <- semiExecRetGen $ do
        f <- lookupVar (Mono.TypedVar "main" Mono.mainType)
        app f (ConstantOperand litUnit)
        pure (ConstantOperand (litI32 0))
    pure (GlobalDefinition (simpleFunc (mkName "main") [] i32 basicBlocks))

genGlobDef :: (Mono.MTypedVar, Mono.MExpr) -> Gen' [Definition]
genGlobDef (v, e) = case e of
    An.Fun p (body, _) ->
        fmap (map GlobalDefinition) (genClosureWrappedFunDef v p body)
    _ -> nyi $ "Global non-function defs: " ++ show e

genClosureWrappedFunDef
    :: Mono.MTypedVar -> (String, Mono.Type) -> Mono.MExpr -> Gen' [Global]
genClosureWrappedFunDef var p body = do
    let name = mangleName var
    fName <- newName'' (unName name `mappend` fromString "_func")
    (f, gs) <- genFunDef' (fName, [], p, body)
    let fRef = LLConst.GlobalReference (LLType.ptr (typeOf f)) fName
    let capturesType = LLType.ptr typeUnit
    let captures = LLConst.Null capturesType
    let closure = litStruct [captures, fRef]
    let closureDef = simpleGlobVar name (typeOf closure) closure
    pure (closureDef : f : gs)

genFunDef
    :: (Name, [Mono.MTypedVar], (String, Mono.Type), Mono.MExpr) -> Gen' [Global]
genFunDef = fmap (uncurry (:)) . genFunDef'

genFunDef'
    :: (Name, [Mono.MTypedVar], (String, Mono.Type), Mono.MExpr)
    -> Gen' (Global, [Global])
genFunDef' (name, fvs, (p, pt), body) = do
    assign currentBlockLabel (mkName "entry")
    assign currentBlockInstrs []

    capturesName <- newName' "captures"
    let capturesType = LLType.ptr typeUnit
    let capturesRef = LocalReference capturesType capturesName

    let ptv = Mono.TypedVar p pt
    let pt' = toLlvmType pt
    p' <- newName' p
    let pRef = LocalReference pt' p'

    (rt, Out basicBlocks globStrings lambdaFuncs) <- semiExecRetGen
        (withVar ptv pRef (genExtractCaptures capturesRef fvs (genExpr body)))

    let ss = map globStrVar globStrings
    ls <- concat <$> mapM genFunDef lambdaFuncs


    let fParams = [parameter capturesName capturesType, parameter p' pt']
    let f = simpleFunc name fParams rt basicBlocks

    pure (f, ss ++ ls)

simpleFunc :: Name -> [Parameter] -> Type -> [BasicBlock] -> Global
simpleFunc n ps rt bs = Function
    { LLGlob.linkage = LLLink.External
    , LLGlob.visibility = LLVis.Default
    , LLGlob.dllStorageClass = Nothing
    , LLGlob.callingConvention = callConv
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
    , LLGlob.metadata = []
    }

globStrVar :: (Name, String) -> Global
globStrVar (name, str) =
    let bytes = UTF8.String.encode str
    in
        simpleGlobVar
            name
            (ArrayType (fromIntegral (length bytes)) i8)
            (LLConst.Array i8 (map (litI8) bytes))

simpleGlobVar :: Name -> Type -> LLConst.Constant -> Global
simpleGlobVar name t init = GlobalVariable
    { LLGlob.name = name
    , LLGlob.linkage = LLLink.External
    , LLGlob.visibility = LLVis.Default
    , LLGlob.dllStorageClass = Nothing
    , LLGlob.threadLocalMode = Nothing
    , LLGlob.addrSpace = LLAddr.AddrSpace 0
    , LLGlob.unnamedAddr = Nothing
    , LLGlob.isConstant = True
    , LLGlob.type' = t
    , LLGlob.initializer = Just init
    , LLGlob.section = Nothing
    , LLGlob.comdat = Nothing
    , LLGlob.alignment = 0
    , LLGlob.metadata = []
    }

parameter :: Name -> Type -> LLGlob.Parameter
parameter p pt = LLGlob.Parameter pt p []

withGlobDefSigs
    :: MonadReader Env m => [(Mono.MTypedVar, Mono.MExpr)] -> m a -> m a
withGlobDefSigs = locally globalEnv . Map.union . Map.fromList . map
    (\(v@(Mono.TypedVar _ t), _) ->
        ( v
        , ConstantOperand
            (LLConst.GlobalReference (LLType.ptr (toLlvmType t)) (mangleName v))
        )
    )

genExtractCaptures :: Operand -> [Mono.MTypedVar] -> Gen a -> Gen a
genExtractCaptures capturesPtrGeneric fvs ga = if null fvs
    then ga
    else do
        let capturesType = typeCaptures fvs
        capturesPtr <- emitAnon
            (bitcast capturesPtrGeneric (LLType.ptr capturesType))
        captures <- emitAnon (load capturesPtr)
        captureVals <- mapM
            (\(Mono.TypedVar x _, i) -> emitReg' x (extractvalue captures [i]))
            (zip fvs [0 ..])
        withVars (zip fvs captureVals) ga

genExpr :: Mono.MExpr -> Gen Operand
genExpr = \case
    An.Lit c -> fmap ConstantOperand (genConst c)
    An.Var (An.TypedVar x t) -> lookupVar (An.TypedVar x t)
    An.App f e -> genApp f e
    An.If p c a -> genIf p c a
    An.Fun p b -> genLambda p b
    An.Let ds b -> genLet ds b

-- | Convert to the LLVM representation of a type in an expression-context.
toLlvmType :: Mono.Type -> Type
toLlvmType = \case
    Mono.TPrim tc -> case tc of
        TUnit -> typeUnit
        TInt -> i64
        TDouble -> double
        TChar -> i32
        TStr -> LLType.ptr i8
        TBool -> i1
    Mono.TFun a r -> typeStruct
        [ LLType.ptr typeUnit
        , LLType.ptr (typeClosureFun (toLlvmType a) (toLlvmType r))
        ]

genConst :: An.Const -> Gen LLConst.Constant
genConst = \case
    An.Unit -> pure litUnit
    An.Int n -> pure $ litI64 n
    An.Double x -> pure $ litDouble x
    An.Char c -> pure $ litI32 (Data.Char.ord c)
    An.Str s -> do
        var <- newName "strlit"
        scribe outStrings [(var, s)]
        pure $ LLConst.GlobalReference (LLType.ptr i8) var
    An.Bool b -> pure $ litBool b

lookupVar :: Mono.MTypedVar -> Gen Operand
lookupVar x = do
    mayLocal <- views localEnv (Map.lookup x)
    mayGlobPtr <- views globalEnv (Map.lookup x)
    case (mayLocal, mayGlobPtr) of
        (Just local, _) -> pure local
        (Nothing, Just globPtr) -> emitAnon $ load globPtr
        (Nothing, Nothing) -> ice $ "Undefined variable " ++ show x

genApp :: Mono.MExpr -> Mono.MExpr -> Gen Operand
genApp fe ae = do
    a <- genExpr ae
    case fe of
        An.Var (An.TypedVar "printInt" _) ->
            emitAnon (callExtern "printInt" typeUnit [a])
        _ -> do
            closure <- genExpr fe
            app closure a

app :: Operand -> Operand -> Gen Operand
app closure arg = do
    captures <- emitReg' "captures" (extractvalue closure [0])
    f <- emitReg' "function" (extractvalue closure [1])
    emitAnon $ call f [captures, arg]

genIf :: Mono.MExpr -> Mono.MExpr -> Mono.MExpr -> Gen Operand
genIf pred conseq alt = do
    conseqL <- newName "consequent"
    altL <- newName "alternative"
    nextL <- newName "next"
    predV <- genExpr pred
    commitToNewBlock (condbr predV conseqL altL) conseqL
    conseqV <- genExpr conseq
    fromConseqL <- use currentBlockLabel
    commitToNewBlock (br nextL) altL
    altV <- genExpr alt
    fromAltL <- use currentBlockLabel
    commitToNewBlock (br nextL) nextL
    emitAnon (phi [(conseqV, fromConseqL), (altV, fromAltL)])

genLet :: Mono.Defs -> Mono.MExpr -> Gen Operand
genLet (Mono.Defs ds) b = do
    let (vs, es) = unzip (Map.toList ds)
    let (ns, ts) = unzip (map (\(Mono.TypedVar n t) -> (n, t)) vs)
    ns' <- mapM newName ns
    let ts' = map toLlvmType ts
    withDefSigs (zip vs ns') (mapM genDef (zip3 ns' ts' es) *> genExpr b)

withDefSigs :: [(Mono.MTypedVar, Name)] -> Gen a -> Gen a
withDefSigs = locally localEnv . Map.union . Map.fromList . map
    (\(v@(Mono.TypedVar _ t), n') -> (v, LocalReference (toLlvmType t) n'))

-- TODO: Change global defs to a new type that can be generated by llvm.  As it
--       is now, global non-function variables can't be straight-forwardly
--       generated in general. Either, initialization is delayed until program
--       start, or an interpretation step is added between monomorphization and
--       codegen that evaluates all expressions in relevant contexts, like
--       constexprs.
genDef :: (Name, Type, Mono.MExpr) -> Gen ()
genDef (n, t, e) = genExpr e >>= genVar n t

genVar :: Name -> Type -> Operand -> Gen ()
genVar var t val = emitReg var (alloca t) >>= emit . store val

-- | A lambda is a pair of a captured environment and a function.  The captured
--   environment must be on the heap, since the closure value needs to be of
--   some specific size, regardless of what the closure captures, so that
--   closures of same types but different captures can be used interchangeably.
--
--   The first parameter of the function is a pointer to an environment of
--   captures and the second parameter is the lambda parameter.
--
--   Inside of the function, first all the captured variables are extracted from
--   the environment, then the body of the function is run.
genLambda :: (String, Mono.Type) -> (Mono.MExpr, Mono.Type) -> Gen Operand
genLambda p@(px, pt) (b, bt) = do
    let fvs = Set.toList (Set.delete (Mono.TypedVar px pt) (freeVars b))
    captures <- genBoxGeneric =<< genStruct =<< sequence (map lookupVar fvs)
    fname <- newName "lambda_func"
    let ft = typeClosureFun (toLlvmType pt) (toLlvmType bt)
    let f = ConstantOperand (LLConst.GlobalReference (LLType.ptr ft) fname)
    scribe outFuncs [(fname, fvs, p, b)]
    genStruct [captures, f]

genStruct :: [Operand] -> Gen Operand
genStruct xs = do
    let t = typeStruct (map typeOf xs)
    foldlM
        (\s (i, x) -> emitReg' "acc" (insertvalue s x [i]))
        (ConstantOperand (LLConst.Undef t))
        (zip [0 ..] xs)

genBoxGeneric :: Operand -> Gen Operand
genBoxGeneric x = do
    let t = typeOf x
    ptrGeneric <- genMalloc =<< genSizeOf t
    ptr <- emitAnon (bitcast ptrGeneric (LLType.ptr t))
    emit (store x ptr)
    pure ptrGeneric

genSizeOf :: Type -> Gen Operand
genSizeOf t = do
    let ptrT = LLType.ptr t
    p <- emitReg'
        "size_ptr"
        (getelementptr
            ptrT
            (ConstantOperand (LLConst.Null ptrT))
            [ConstantOperand (litI64 1)]
        )
    emitReg' "size" (ptrtoint p i64)

genMalloc :: Operand -> Gen Operand
genMalloc size = emitAnon (callExtern "malloc" (LLType.ptr typeUnit) [size])

withVars :: [(Mono.MTypedVar, Operand)] -> Gen a -> Gen a
withVars = flip (foldr (uncurry withVar))

withVar :: Mono.MTypedVar -> Operand -> Gen a -> Gen a
withVar x v = locally localEnv (Map.insert x v)

emit :: Instruction -> Gen ()
emit instr = emit' (Do instr)

emit' :: (Named Instruction) -> Gen ()
emit' = modifying currentBlockInstrs . (:)

emitReg :: Name -> FunInstruction -> Gen Operand
emitReg reg (WithRetType instr rt) = do
    emit' (reg := instr)
    pure (LocalReference rt reg)

emitReg' :: String -> FunInstruction -> Gen Operand
emitReg' s instr = newName s >>= flip emitReg instr

emitAnon :: FunInstruction -> Gen Operand
emitAnon instr = newAnonRegister >>= flip emitReg instr

commitFinalFuncBlock :: Terminator -> Gen ()
commitFinalFuncBlock t = commitToNewBlock
    t
    (ice "Continued gen after final block of function was already commited")

commitToNewBlock :: Terminator -> Name -> Gen ()
commitToNewBlock t l = do
    n <- use currentBlockLabel
    is <- uses currentBlockInstrs reverse
    scribe outBlocks [BasicBlock n is (Do t)]
    assign currentBlockLabel l
    assign currentBlockInstrs []

newAnonRegister :: Gen Name
newAnonRegister = fmap UnName (registerCount <<+= 1)

newName :: String -> Gen Name
newName = lift . newName'

newName' :: String -> Gen' Name
newName' s = fmap (mkName . (s ++) . show) (registerCount <<+= 1)

newName'' :: ShortByteString -> Gen' Name
newName'' s =
    fmap (Name . (mappend s) . fromString . show) (registerCount <<+= 1)

-- TODO: Shouldn't need a return type parameter. Should look at global list of hidden
-- builtins or something.
callExtern :: String -> Type -> [Operand] -> FunInstruction
callExtern f rt as = WithRetType
    (Call
        { tailCallKind = Just Tail
        , callingConvention = callConv
        , returnAttributes = []
        , function = Right $ ConstantOperand $ LLConst.GlobalReference
            (LLType.ptr (FunctionType rt (map typeOf as) False))
            (mkName f)
        , arguments = map (, []) as
        , functionAttributes = []
        , metadata = []
        }
    )
    rt

condbr :: Operand -> Name -> Name -> Terminator
condbr c t f = CondBr c t f []

br :: Name -> Terminator
br = flip Br []

ret :: Operand -> Terminator
ret = flip Ret [] . Just

ptrtoint :: Operand -> Type -> FunInstruction
ptrtoint p t = WithRetType (PtrToInt {operand0 = p, type' = t, metadata = []}) t

bitcast :: Operand -> Type -> FunInstruction
bitcast x t = WithRetType (BitCast x t []) t

insertvalue :: Operand -> Operand -> [Word32] -> FunInstruction
insertvalue s e is = WithRetType (InsertValue s e is []) (typeOf s)

extractvalue :: Operand -> [Word32] -> FunInstruction
extractvalue struct is = WithRetType
    (ExtractValue {aggregate = struct, indices' = is, metadata = []})
    (getIndexed (typeOf struct) is)

getelementptr :: Type -> Operand -> [Operand] -> FunInstruction
getelementptr rt p is = WithRetType
    (GetElementPtr {inBounds = False, address = p, indices = is, metadata = []})
    rt

store :: Operand -> Operand -> Instruction
store srcVal destPtr = Store
    { volatile = False
    , address = destPtr
    , value = srcVal
    , maybeAtomicity = Nothing
    , alignment = 0
    , metadata = []
    }

load :: Operand -> FunInstruction
load p = WithRetType
    (Load
        { volatile = False
        , address = p
        , maybeAtomicity = Nothing
        , alignment = 0
        , metadata = []
        }
    )
    (getPointee (typeOf p))

phi :: [(Operand, Name)] -> FunInstruction
phi = \case
    [] -> ice "phi was given empty list of cases"
    cs@((op, _) : _) -> let t = typeOf op in WithRetType (Phi t cs []) t

call :: Operand -> [Operand] -> FunInstruction
call f as = WithRetType
    (Call
        { tailCallKind = Just Tail
        , callingConvention = callConv
        , returnAttributes = []
        , function = Right f
        , arguments = map (, []) as
        , functionAttributes = []
        , metadata = []
        }
    )
    (getFunRet (getPointee (typeOf f)))

alloca :: Type -> FunInstruction
alloca t = WithRetType (Alloca t Nothing 0 []) t

litI64 :: Int -> LLConst.Constant
litI64 = LLConst.Int 64 . toInteger

litI32 :: Int -> LLConst.Constant
litI32 = LLConst.Int 32 . toInteger

litI8 :: Integral n => n -> LLConst.Constant
litI8 = LLConst.Int 32 . toInteger

litBool :: Bool -> LLConst.Constant
litBool = LLConst.Int 1 . bool 1 0

litDouble :: Double -> LLConst.Constant
litDouble = LLConst.Float . LLFloat.Double

litStruct :: [LLConst.Constant] -> LLConst.Constant
litStruct = LLConst.Struct Nothing False

litUnit :: LLConst.Constant
litUnit = litStruct []

typeClosureFun :: Type -> Type -> Type
typeClosureFun pt rt = FunctionType
    { resultType = rt
    , argumentTypes = [LLType.ptr (typeCaptures []), pt]
    , isVarArg = False
    }

typeCaptures :: [Mono.MTypedVar] -> Type
typeCaptures = typeStruct . map (\(Mono.TypedVar _ t) -> toLlvmType t)

typeStruct :: [Type] -> Type
typeStruct ts = StructureType {isPacked = False, elementTypes = ts}

typeUnit :: Type
typeUnit = StructureType {isPacked = False, elementTypes = []}

getFunRet :: Type -> Type
getFunRet = \case
    FunctionType rt _ _ -> rt
    t -> ice $ "Tried to get return type of non-function type " ++ pretty t

getPointee :: Type -> Type
getPointee = \case
    LLType.PointerType t _ -> t
    t -> ice $ "Tried to get pointee of non-function type " ++ pretty t

getMembers :: Type -> [Type]
getMembers = \case
    StructureType _ members -> members
    t -> ice $ "Tried to get member types of non-struct type " ++ pretty t

getIndexed :: Type -> [Word32] -> Type
getIndexed = foldl (\t i -> getMembers t !! (fromIntegral i))

mangleName :: Mono.MTypedVar -> Name
mangleName (Mono.TypedVar x t) = mkName (x ++ ":" ++ mangleType t)

mangleType :: Mono.Type -> String
mangleType = \case
    Mono.TFun p r -> mangleType p ++ "->" ++ mangleType r
    Mono.TPrim c -> pretty c

unName :: Name -> ShortByteString
unName = \case
    Name s -> s
    UnName n -> fromString (show n)

instance Pretty Type where
    pretty' _ = show . Prettyprint.pretty

instance Pretty Name where
    pretty' _ = show . Prettyprint.pretty

instance Pretty Module where
    pretty' _ = show . Prettyprint.pretty
