{-# LANGUAGE OverloadedStrings, LambdaCase, TupleSections, FlexibleContexts #-}

-- | Generation of LLVM IR code from our monomorphic AST.
module Codegen (codegen) where

import LLVM.AST hiding (args, Store)
import LLVM.AST.Typed
import LLVM.AST.Type hiding (ptr)
import LLVM.AST.DataLayout
import qualified LLSubprog
import qualified LLCompunit
import qualified LLVM.AST.Operand as LLOp
import qualified LLVM.AST.Type as LLType
import qualified LLVM.AST.Constant as LLConst
import Data.String
import System.FilePath
import Control.Monad.Writer
import Control.Monad.Except
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Word
import Data.Maybe
import Data.Foldable
import Data.List
import Data.Function
import Data.Functor
import Data.Functor.Identity
import Data.Bifunctor
import Control.Applicative
import Lens.Micro.Platform (use, assign, view)

import Misc
import SrcPos
import FreeVars
import qualified Monomorphic as M
import Monomorphic hiding (Type, Const)
import Selections
import Gen
import Extern


codegen :: DataLayout -> FilePath -> Program -> Either GenErr Module
codegen layout moduleFilePath (Program (Topo defs) tdefs externs) = runExcept $ do
    (tdefs', externs', globDefs) <-
        let (enums, tdefs'') = runIdentity (runGen' (defineDataTypes tdefs))
            defs' = defToVarDefs =<< defs
            (funDefs, varDefs) = separateFunDefs defs'
        in  runGen'
            $ augment enumTypes enums
            $ augment dataTypes tdefs''
            $ withBuiltins
            $ withExternSigs externs
            $ withGlobDefSigs (map (second unpos) defs')
            $ do
                  es <- genExterns externs
                  funDefs' <- mapM genGlobFunDef funDefs
                  varDecls <- mapM genGlobVarDecl varDefs
                  init_ <- genInit moduleFilePath varDefs
                  main <- genMain
                  let ds = main : init_ ++ join funDefs' ++ varDecls
                  pure (tdefs'', es, ds)
    pure $ Module
        { moduleName = fromString ((takeBaseName moduleFilePath))
        , moduleSourceFileName = fromString moduleFilePath
        , moduleDataLayout = Just layout
        , moduleTargetTriple = Nothing
        , moduleDefinitions = concat
                                  [ map
                                      (\(n, tmax) ->
                                          TypeDefinition n (Just (typeStruct tmax))
                                      )
                                      (Map.toList tdefs')
                                  , defineBuiltinsHidden
                                  , externs'
                                  , globDefs
                                  , globMetadataDefs
                                  ]
        }
  where
    withGlobDefSigs sigs ga = do
        sigs' <- forM sigs $ \(v@(TypedVar x t), (us, _)) -> do
            t' <- genType' t
            pure
                ( v
                , ConstantOperand $ LLConst.GlobalReference
                    (LLType.ptr t')
                    (mkName (mangleName (x, us)))
                )
        augment env (Map.fromList sigs') ga

    fileId = MetadataNodeID 1
    debugInfoVersionId = MetadataNodeID 2
    globMetadataDefs =
        [ MetadataNodeDefinition compileUnitId
            $ DINode (LLOp.DIScope (LLOp.DICompileUnit compileUnitDef))
        , MetadataNodeDefinition fileId $ DINode (LLOp.DIScope (LLOp.DIFile fileDef))
        , MetadataNodeDefinition debugInfoVersionId $ MDTuple
            [ Just (MDValue (litI32 2))
            , Just (MDString "Debug Info Version")
            , Just (MDValue (litI32 3))
            ]
        , NamedMetadataDefinition "llvm.dbg.cu" [compileUnitId]
        , NamedMetadataDefinition "llvm.module.flags" [debugInfoVersionId]
        ]
    compileUnitDef = LLCompunit.CompileUnit
        { LLCompunit.language = let unstandardized_c = 1 in unstandardized_c
        , LLCompunit.file = MDRef fileId
        , LLCompunit.producer = "carth version alpha"
        , LLCompunit.optimized = False
        , LLCompunit.flags = ""
        , LLCompunit.runtimeVersion = 0
        , LLCompunit.splitDebugFileName = ""
        , LLCompunit.emissionKind = LLOp.FullDebug
        , LLCompunit.enums = []
        , LLCompunit.retainedTypes = []
        , LLCompunit.globals = []
        , LLCompunit.imports = []
        , LLCompunit.macros = []
        , LLCompunit.dWOId = 0
        , LLCompunit.splitDebugInlining = False
        , LLCompunit.debugInfoForProfiling = False
        , LLCompunit.nameTableKind = LLOp.NameTableKindNone
        , LLCompunit.debugBaseAddress = False
        }
    fileDef =
        let (dir, file) = splitFileName moduleFilePath
        in  LLOp.File { LLSubprog.filename = fromString file
                      , LLSubprog.directory = fromString dir
                      , LLSubprog.checksum = Nothing
                      }

-- | A data-type is a tagged union, and we represent it in LLVM as a struct
--   where, if there are more than 1 variant, the first element is the
--   variant-index. The variant index is represented as an integer with the
--   smallest width 2^n that can fit all variants. The rest of the elements are
--   the field-types of the largest variant wrt allocation size.
--
--   If none of the variants of the data-type has any members, we say it's an
--   enumeration, which is represented as a single integer, equal to the size it
--   would have been as a tag. If further there's only a single variant, the
--   data-type is represented as `{}`.
defineDataTypes :: Datas -> Gen'T Identity (Map Name Word32, Map Name [Type])
defineDataTypes datasEnums = do
    let (enums, datas) = partition (all null . snd) (Map.toList datasEnums)
    let enums' = Map.fromList $ map
            (\(tc, vs) ->
                ( mkName (mangleTConst tc)
                , fromMaybe 0 (tagBitWidth (fromIntegral (length vs)))
                )
            )
            enums
    datas'' <- mfix $ \datas' ->
        fmap Map.fromList
            $ augment enumTypes enums'
            $ augment dataTypes datas'
            $ forM datas
            $ \(tc, vs) -> do
                  let n = mkName (mangleTConst tc)
                  let totVariants = fromIntegral (length vs)
                  ts <- mapM (genVariantType totVariants) vs
                  sizedTs <- mapM (\t -> sizeof (typeStruct t) <&> (, t)) ts
                  if null sizedTs
                      then ice ("defineDataTypes: sizedTs empty for " ++ show n)
                      else pure (n, snd (maximum sizedTs))
    pure (enums', datas'')

genMain :: Gen' Definition
genMain = do
    let tDummyCaptures = LLType.ptr typeUnit
    let tDummyParam = typeUnit
    let init_ = ConstantOperand $ LLConst.GlobalReference
            (LLType.ptr (FunctionType LLType.void [tDummyCaptures, tDummyParam] False))
            (mkName "carth_init")
    assign currentBlockLabel (mkName "entry")
    assign currentBlockInstrs []
    Out basicBlocks _ _ _ <- execWriterT $ do
        emitDo' =<< callBuiltin "install_stackoverflow_handler" []
        emitDo (callIntern Nothing init_ [(null' tDummyCaptures, []), (litUnit, [])])
        f <- lookupVar (TypedVar "main" mainType)
        _ <- app Nothing f (VLocal litUnit)
        commitFinalFuncBlock (ret (litI32 0))
    pure (GlobalDefinition (externFunc (mkName "main") [] i32 basicBlocks []))

separateFunDefs :: [VarDef] -> ([FunDef], [VarDef])
separateFunDefs = partitionWith $ \(lhs, WithPos dpos (ts, e)) -> case e of
    Fun f -> Left (lhs, WithPos dpos (ts, f))
    _ -> Right (lhs, WithPos dpos (ts, e))

genInit :: FilePath -> [VarDef] -> Gen' [Definition]
genInit moduleFp ds = do
    let name = mkName "carth_init"
    let pos = SrcPos moduleFp 1 1
    let param = TypedVar "_" (TConst tUnit)
    let genDefs =
            forM_ ds genDefineGlobVar *> commitFinalFuncBlock retVoid $> LLType.void
    fmap (uncurry ((:) . GlobalDefinition)) $ genFunDef (name, [], pos, param, genDefs)

genDefineGlobVar :: VarDef -> Gen ()
genDefineGlobVar (TypedVar v _, WithPos pos (ts, e)) = do
    let name = mkName (mangleName (v, ts))
    e' <- getLocal =<< genExpr (Expr (Just pos) e)
    let ref = LLConst.GlobalReference (LLType.ptr (typeOf e')) name
    emitDo (store e' (ConstantOperand ref))

genGlobVarDecl :: VarDef -> Gen' Definition
genGlobVarDecl (TypedVar v t, WithPos _ (ts, _)) = do
    let name = mkName (mangleName (v, ts))
    t' <- genType' t
    pure (GlobalDefinition (simpleGlobVar name t' (LLConst.Undef t')))

genGlobFunDef :: FunDef -> Gen' [Definition]
genGlobFunDef (TypedVar v _, WithPos dpos (ts, (p, (body, rt)))) = do
    let var = (v, ts)
    let name = mangleName var
    assign lambdaParentFunc (Just name)
    assign outerLambdaN 1
    let fName = mkName (name ++ "_func")
    (f, gs) <- genFunDef (fName, [], dpos, p, genTailExpr body *> genRetType rt)
    let fRef = LLConst.GlobalReference (LLType.ptr (typeOf f)) fName
    let capturesType = LLType.ptr typeUnit
    let captures = LLConst.Null capturesType
    let closure = litStruct [captures, fRef]
    let closureDef = simpleGlobConst (mkName name) (typeOf closure) closure
    pure (GlobalDefinition closureDef : GlobalDefinition f : gs)

genTailExpr :: Expr -> Gen ()
genTailExpr (Expr pos expr) = locally srcPos (pos <|>) $ do
    parent <- use lambdaParentFunc <* assign lambdaParentFunc Nothing
    case expr of
        App f e _ -> genTailApp f e
        If p c a -> genTailIf p c a
        Let d b -> genTailLet d b
        Match e cs tbody -> genTailMatch e cs =<< genType tbody
        _ -> genTailReturn =<< case expr of
            Fun (p, b) -> assign lambdaParentFunc parent *> genExprLambda p b
            _ -> genExpr (Expr pos expr)

genTailReturn :: Val -> Gen ()
genTailReturn v = if typeOf v == typeUnit
    then commitFinalFuncBlock retVoid
    else commitFinalFuncBlock . ret =<< getLocal v

genExpr :: Expr -> Gen Val
genExpr (Expr pos expr) = locally srcPos (pos <|>) $ do
    parent <- use lambdaParentFunc <* assign lambdaParentFunc Nothing
    case expr of
        Lit c -> genConst c
        Var x -> lookupVar x
        App f e _ -> genApp f e
        If p c a -> genIf p c a
        Fun (p, b) -> assign lambdaParentFunc parent *> genExprLambda p b
        Let d b -> genLet d b
        Match e cs tbody -> genMatch e cs =<< genType tbody
        Ction c -> genCtion c
        Sizeof t -> (VLocal . litI64 . fromIntegral) <$> ((lift . sizeof) =<< genType t)
        Deref e -> genDeref e
        Store x p -> genStore x p
        Absurd t -> fmap (VLocal . undef) (genType t)
        Transmute epos e t u -> genTransmute epos e t u

genExprLambda :: TypedVar -> (Expr, M.Type) -> Gen Val
genExprLambda p (b, bt) = do
    let fvXs = Set.toList (Set.delete p (freeVars b))
    bt' <- genRetType bt
    genLambda fvXs p (genTailExpr b, bt')

genConst :: M.Const -> Gen Val
genConst = \case
    Int n -> pure (VLocal (litI64 n))
    F64 x -> pure (VLocal (litF64 x))
    Str s -> genStrLit s

genStrLit :: String -> Gen Val
genStrLit s = do
    var <- newName "strlit"
    scribe outStrings [(var, s)]
    pure $ VVar $ ConstantOperand (LLConst.GlobalReference (LLType.ptr typeStr) var)

genTailApp :: Expr -> Expr -> Gen ()
genTailApp fe' ae' = genBetaReduceApp genTailExpr genTailReturn Tail (fe', [ae'])

genApp :: Expr -> Expr -> Gen Val
genApp fe' ae' = genBetaReduceApp genExpr pure NoTail (fe', [ae'])

-- | Beta-reduction and closure application
genBetaReduceApp
    :: (Expr -> Gen a) -> (Val -> Gen a) -> TailCallKind -> (Expr, [Expr]) -> Gen a
genBetaReduceApp genExpr' returnMethod tail' applic = view env >>= \env' ->
    case applic of
        (Expr _ (Fun (p, (b, _))), ae : aes) -> do
            a <- genExpr ae
            withVal p a (genBetaReduceApp genExpr' returnMethod tail' (b, aes))
        (Expr _ (App fe ae _), aes) ->
            genBetaReduceApp genExpr' returnMethod tail' (fe, ae : aes)
        (fe, []) -> genExpr' fe
        (Expr _ (Var x), aes) | not (Map.member x env') ->
            returnMethod =<< genAppBuiltinVirtual x (map genExpr aes)
        (fe, aes) -> do
            f <- genExpr fe
            as <- mapM genExpr (init aes)
            closure <- foldlM (app (Just NoTail)) f as
            arg <- genExpr (last aes)
            returnMethod =<< app (Just tail') closure arg

app :: Maybe TailCallKind -> Val -> Val -> Gen Val
app tailkind closure a = do
    closure' <- getLocal closure
    captures <- emitReg "captures" =<< extractvalue closure' [0]
    f <- emitReg "function" =<< extractvalue closure' [1]
    a' <- getLocal a
    let as = [(captures, []), (a', [])]
    let rt = getFunRet (getPointee (typeOf f))
    fmap VLocal $ if rt == LLType.void
        then emitDo (callIntern tailkind f as) $> litUnit
        else emitAnonReg $ WithRetType (callIntern tailkind f as) rt

genTailIf :: Expr -> Expr -> Expr -> Gen ()
genTailIf pred' conseq alt = do
    predV <- genExpr pred'
    genTailCondBr predV (genTailExpr conseq) (genTailExpr alt)

genIf :: Expr -> Expr -> Expr -> Gen Val
genIf pred' conseq alt = do
    predV <- genExpr pred'
    genCondBr predV (genExpr conseq) (genExpr alt)

genTailCondBr :: Val -> Gen () -> Gen () -> Gen ()
genTailCondBr predV genConseq genAlt = do
    predV' <- emitAnonReg . flip trunc i1 =<< getLocal predV
    conseqL <- newName "consequent"
    altL <- newName "alternative"
    commitToNewBlock (condbr predV' conseqL altL) conseqL
    genConseq
    assign currentBlockLabel altL
    genAlt

genCondBr :: Val -> Gen Val -> Gen Val -> Gen Val
genCondBr predV genConseq genAlt = do
    predV' <- emitAnonReg . flip trunc i1 =<< getLocal predV
    conseqL <- newName "consequent"
    altL <- newName "alternative"
    nextL <- newName "next"
    commitToNewBlock (condbr predV' conseqL altL) conseqL
    conseqV <- getLocal =<< genConseq
    fromConseqL <- use currentBlockLabel
    commitToNewBlock (br nextL) altL
    altV <- getLocal =<< genAlt
    fromAltL <- use currentBlockLabel
    commitToNewBlock (br nextL) nextL
    fmap VLocal (emitAnonReg (phi [(conseqV, fromConseqL), (altV, fromAltL)]))

genTailLet :: Def -> Expr -> Gen ()
genTailLet d = genLet' d . genTailExpr

genLet :: Def -> Expr -> Gen Val
genLet d = genLet' d . genExpr

genLet' :: Def -> Gen a -> Gen a
genLet' def genBody = case def of
    VarDef (lhs, WithPos pos (_, rhs)) ->
        genExpr (Expr (Just pos) rhs) >>= \rhs' -> withVal lhs rhs' genBody
    RecDefs ds -> do
        (binds, cs) <- fmap unzip $ forM ds $ \case
            (lhs, WithPos _ (_, (p, (fb, fbt)))) -> do
                let fvXs = Set.toList (Set.delete p (freeVars fb))
                tcaptures <- fmap typeStruct (mapM (\(TypedVar _ t) -> genType t) fvXs)
                captures <- genHeapAllocGeneric tcaptures
                fbt' <- genRetType fbt
                lam <-
                    getVar =<< genLambda' p (genTailExpr fb, fbt') (VLocal captures) fvXs
                pure ((lhs, lam), (captures, fvXs))
        withVars binds $ do
            forM_ cs (uncurry populateCaptures)
            genBody

genTailMatch :: Expr -> DecisionTree -> Type -> Gen ()
genTailMatch m dt tbody = do
    m' <- getLocal =<< genExpr m
    genTailDecisionTree tbody dt (newSelections m')

genMatch :: Expr -> DecisionTree -> Type -> Gen Val
genMatch m dt tbody = do
    -- TODO: Do we have to convert it to an operand here already? Keeping it as
    --       Val would probably eliminate a needless stack allocation.
    m' <- getLocal =<< genExpr m
    genDecisionTree tbody dt (newSelections m')

genTailDecisionTree :: Type -> DecisionTree -> Selections Operand -> Gen ()
genTailDecisionTree = genDecisionTree' genTailExpr genTailCondBr genTailCases

genDecisionTree :: Type -> DecisionTree -> Selections Operand -> Gen Val
genDecisionTree = genDecisionTree' genExpr genCondBr genCases

genDecisionTree'
    :: (Expr -> Gen a)
    -> (Val -> Gen a -> Gen a -> Gen a)
    -> ( Type
       -> Selections Operand
       -> [Name]
       -> [DecisionTree]
       -> DecisionTree
       -> Gen a
       )
    -> Type
    -> DecisionTree
    -> Selections Operand
    -> Gen a
genDecisionTree' genExpr' genCondBr' genCases' tbody =
    let genDecisionLeaf (bs, e) selections = do
            bs' <- selectVarBindings selAs selSub selDeref selections bs
            withLocals bs' (genExpr' e)

        genDecisionSwitchIx selector cs def selections = do
            let (variantIxs, variantDts) = unzip (Map.toAscList cs)
            (m, selections') <- select selAs selSub selDeref selector selections
            mVariantIx <- case typeOf m of
                IntegerType _ -> pure m
                _ -> emitReg "found_variant_ix" =<< extractvalue m [0]
            let ixBits = getIntBitWidth (typeOf mVariantIx)
            let litIxInt = LLConst.Int ixBits
            variantLs <- mapM (newName . (++ "_") . ("variant_" ++) . show) variantIxs
            defaultL <- newName "default"
            let dests' = zip (map litIxInt variantIxs) variantLs
            commitToNewBlock (switch mVariantIx defaultL dests') defaultL
            genCases' tbody selections' variantLs variantDts def

        genDecisionSwitchStr selector cs def selections = do
            (matchee, selections') <- select selAs selSub selDeref selector selections
            let cs' = Map.toAscList cs
            let genCase (s, dt) next = do
                    s' <- genStrLit s
                    isMatch <- genStrEq (VLocal matchee) s'
                    -- Do some wrapping to preserve effect/Gen order
                    pure $ genCondBr' isMatch (genDT dt selections') next
            join (foldrM genCase (genDT def selections') cs')

        genDT = \case
            M.DLeaf l -> genDecisionLeaf l
            M.DSwitch selector cs def -> genDecisionSwitchIx selector cs def
            M.DSwitchStr selector cs def -> genDecisionSwitchStr selector cs def
    in  genDT

genTailCases
    :: Type -> Selections Operand -> [Name] -> [DecisionTree] -> DecisionTree -> Gen ()
genTailCases tbody selections variantLs variantDts def = do
    genTailDecisionTree tbody def selections
    forM_ (zip variantLs variantDts) $ \(l, dt) -> do
        assign currentBlockLabel l
        genTailDecisionTree tbody dt selections

genCases
    :: Type -> Selections Operand -> [Name] -> [DecisionTree] -> DecisionTree -> Gen Val
genCases tbody selections variantLs variantDts def = do
    nextL <- newName "next"
    let genDT dt = liftA2 (,)
                          (getLocal =<< genDecisionTree tbody dt selections)
                          (use currentBlockLabel)
    v <- genDT def
    let genCase l dt = do
            commitToNewBlock (br nextL) l
            genDT dt
    vs <- zipWithM genCase variantLs variantDts
    commitToNewBlock (br nextL) nextL
    fmap VLocal (emitAnonReg (phi (v : vs)))

selAs :: Span -> [M.Type] -> Operand -> Gen Operand
selAs totVariants ts matchee = do
    tvariant <- fmap typeStruct (lift (genVariantType totVariants ts))
    let tgeneric = typeOf matchee
    pGeneric <- emitReg "ction_ptr_nominal" (alloca tgeneric)
    emitDo (store matchee pGeneric)
    p <- emitReg "ction_ptr_structural" (bitcast pGeneric (LLType.ptr tvariant))
    emitReg "ction" (load p)

selSub :: Span -> Word32 -> Operand -> Gen Operand
selSub span' i matchee =
    let tagOffset = if span' > 1 then 1 else 0
    in  emitReg "submatchee" =<< extractvalue matchee (pure (tagOffset + i))

selDeref :: Operand -> Gen Operand
selDeref x = emitAnonReg (load x)

genCtion :: M.Ction -> Gen Val
genCtion (i, span', dataType, as) = do
    lookupEnum dataType & lift >>= \case
        Just 0 -> pure (VLocal litUnit)
        Just w -> pure (VLocal (ConstantOperand (LLConst.Int w i)))
        Nothing -> do
            as' <- mapM genExpr as
            let tag = maybe id
                            ((:) . VLocal . ConstantOperand . flip LLConst.Int i)
                            (tagBitWidth span')
            s <- getLocal =<< genStruct (tag as')
            let t = typeOf s
            let tgeneric = genDatatypeRef dataType
            pGeneric <- emitReg "ction_ptr_nominal" (alloca tgeneric)
            p <- emitReg "ction_ptr_structural" (bitcast pGeneric (LLType.ptr t))
            emitDo (store s p)
            pure (VVar pGeneric)

genDeref :: Expr -> Gen Val
genDeref e = genExpr e >>= \case
    VVar x -> fmap VVar (selDeref x)
    VLocal x -> pure (VVar x)

genStore :: Expr -> Expr -> Gen Val
genStore x p = do
    x' <- getLocal =<< genExpr x
    p' <- genExpr p
    p'' <- getLocal p'
    emitDo (store x' p'')
    pure p'

genTransmute :: SrcPos -> Expr -> M.Type -> M.Type -> Gen Val
genTransmute pos e t u = do
    t' <- genType t
    u' <- genType u
    st <- lift (sizeof t')
    su <- lift (sizeof u')
    if st == su
        then genExpr e >>= transmute t' u'
        else throwError (TransmuteErr pos (t, st) (u, su))

-- | Assumes that the from-type and to-type are of the same size.
transmute :: Type -> Type -> Val -> Gen Val
transmute t u x = case (t, u) of
    (FunctionType _ _ _, _) -> transmuteIce
    (_, FunctionType _ _ _) -> transmuteIce
    (MetadataType, _) -> transmuteIce
    (_, MetadataType) -> transmuteIce
    (LabelType, _) -> transmuteIce
    (_, LabelType) -> transmuteIce
    (TokenType, _) -> transmuteIce
    (_, TokenType) -> transmuteIce
    (VoidType, _) -> transmuteIce
    (_, VoidType) -> transmuteIce

    (IntegerType _, IntegerType _) -> bitcast'
    (IntegerType _, PointerType _ _) ->
        getLocal x >>= \x' -> emitAnonReg (inttoptr x' u) <&> VLocal
    (IntegerType _, FloatingPointType _) -> bitcast'
    (IntegerType _, VectorType _ _) -> bitcast'

    (PointerType pt _, PointerType pu _) | pt == pu -> pure x
                                         | otherwise -> bitcast'
    (PointerType _ _, IntegerType _) ->
        getLocal x >>= \x' -> emitAnonReg (ptrtoint x' u) <&> VLocal
    (PointerType _ _, _) -> stackCast
    (_, PointerType _ _) -> stackCast

    (FloatingPointType _, FloatingPointType _) -> pure x
    (FloatingPointType _, IntegerType _) -> bitcast'
    (FloatingPointType _, VectorType _ _) -> bitcast'

    (VectorType _ vt, VectorType _ vu) | vt == vu -> pure x
                                       | otherwise -> bitcast'
    (VectorType _ _, IntegerType _) -> bitcast'
    (VectorType _ _, FloatingPointType _) -> bitcast'

    (StructureType _ _, _) -> stackCast
    (_, StructureType _ _) -> stackCast
    (ArrayType _ _, _) -> stackCast
    (_, ArrayType _ _) -> stackCast
    (NamedTypeReference _, _) -> stackCast
    (_, NamedTypeReference _) -> stackCast
  where
    transmuteIce = ice $ "transmute " ++ show t ++ " to " ++ show u
    bitcast' = getLocal x >>= \x' -> emitAnonReg (bitcast x' u) <&> VLocal
    stackCast = getVar x >>= \x' -> emitAnonReg (bitcast x' (LLType.ptr u)) <&> VVar

genStrEq :: Val -> Val -> Gen Val
genStrEq s1 s2 = do
    s1' <- getLocal s1
    s2' <- getLocal s2
    b <- emitAnonReg =<< callBuiltin "carth_str_eq" [s1', s2']
    pure (VLocal b)
