{-# LANGUAGE DuplicateRecordFields, GADTs, RankNTypes #-}

-- | Generation of LLVM IR code from our monomorphic AST.
module Back.Codegen (codegen) where

import LLVM.Prelude
import LLVM.AST hiding (args)
import LLVM.AST.Typed
import LLVM.AST.Type hiding (ptr)
import LLVM.AST.DataLayout
import qualified LLVM.AST.Type as LLType
import qualified LLVM.AST.Constant as LLConst
import Data.String
import System.FilePath
import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.List
import Data.Function
import Lens.Micro.Platform (use, assign, view)

import Misc
import FreeVars
import Sizeof (tagBitWidth)
import qualified Back.Low as Ast
import Back.Low hiding (Type, Const)
import Front.TypeAst
import Back.Selections
import Back.Gen
import Back.Extern

instance Select Gen Val where
    selectAs totVariants ts matchee = do
        tvariant <- fmap typeStruct (lift (genVariantType totVariants ts))
        pGeneric <- getVar matchee
        fmap VVar
             (emitReg "ction_ptr_structural" (bitcast pGeneric (LLType.ptr tvariant)))
    selectSub span' i matchee =
        let tagOffset = if span' > 1 then 1 else 0
        in  genIndexStruct matchee [tagOffset + i]
    selectDeref = genDeref

codegen :: DataLayout -> ShortByteString -> FilePath -> Program -> Module
codegen layout triple moduleFilePath (Program (Topo defs) tdefs externs) =
    let (tdefs', externs', globDefs) =
            let (enums, tdefs'') = runGen' (defineDataTypes tdefs)
                defs' = defToVarDefs =<< defs
                (funDefs, varDefs) = separateFunDefs defs'
            in  runGen'
                    $ augment enumTypes enums
                    $ augment dataTypes tdefs''
                    $ withBuiltins
                    $ withExternSigs externs
                    $ withGlobFunSigs funDefs
                    $ withGlobVarSigs varDefs
                    $ do
                          es <- genExterns externs
                          funDefs' <- mapM genGlobFunDef funDefs
                          varDecls <- mapM genGlobVarDecl varDefs
                          init_ <- genInit varDefs
                          main <- genMain
                          let ds = main : init_ ++ join funDefs' ++ varDecls
                          pure (tdefs'', es, ds)
    in  Module
            { moduleName = fromString (takeBaseName moduleFilePath)
            , moduleSourceFileName = fromString moduleFilePath
            , moduleDataLayout = Just layout
            , moduleTargetTriple = Just triple
            , moduleDefinitions = concat
                                      [ map
                                          (\(n, tmax) ->
                                              TypeDefinition n (Just (typeStruct tmax))
                                          )
                                          (Map.toList tdefs')
                                      , defineBuiltinsHidden
                                      , externs'
                                      , globDefs
                                      ]
            }
  where
    withGlobFunSigs sigs ga = do
        sigs' <- forM sigs $ \(v@(TypedVar x t), (us, _)) -> do
            t' <- genType' t
            tf <- getIndexed t' [1 :: Int]
            pure (v, (tf, mkName (mangleName (x, us) ++ "_func")))
        augment globalFunEnv (Map.fromList sigs') ga

    withGlobVarSigs sigs ga = do
        sigs' <- forM sigs $ \(v@(TypedVar x t), (us, _)) -> do
            t' <- genType' t
            pure (v, (LLType.ptr t', mkName (mangleName (x, us))))
        augment globalEnv (Map.fromList sigs') ga

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
defineDataTypes :: Datas -> Gen' (Map Name Word32, Map Name [Type])
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
    let tDummyParam = typeUnit
    let init_ = ConstantOperand $ LLConst.GlobalReference
            (LLType.ptr (FunctionType LLType.void [typeGenericPtr, tDummyParam] False))
            (mkName "carth_init")
    assign currentBlockLabel (mkName "entry")
    assign currentBlockInstrs []
    Out basicBlocks _ _ <- execWriterT $ do
        emitDo' =<< callBuiltin "install_stackoverflow_handler" []
        emitDo (callIntern Nothing init_ [(null' typeGenericPtr, []), (litUnit, [])])
        iof <- lookupVar (TypedVar "main" mainType)
        f <- genIndexStruct iof [0]
        _ <- app' @Val f (VLocal litRealWorld)
        commitFinalFuncBlock (ret (litI32 0))
    pure (GlobalDefinition (externFunc (mkName "main") [] i32 basicBlocks))

separateFunDefs :: [VarDef] -> ([FunDef], [VarDef])
separateFunDefs = partitionWith $ \(lhs, (ts, e)) -> case e of
    Fun f -> Left (lhs, (ts, f))
    _ -> Right (lhs, (ts, e))

genInit :: [VarDef] -> Gen' [Definition]
genInit ds = do
    let name = mkName "carth_init"
    let param = TypedVar "_" tUnit
    let genDefs =
            forM_ ds genDefineGlobVar *> commitFinalFuncBlock retVoid $> LLType.void
    fmap (uncurry ((:) . GlobalDefinition)) $ genFunDef (name, [], param, genDefs)

genDefineGlobVar :: VarDef -> Gen ()
genDefineGlobVar (TypedVar v _, (ts, e)) = do
    let name = mkName (mangleName (v, ts))
    e' <- genExpr e
    let ref = LLConst.GlobalReference (LLType.ptr (typeOf e')) name
    -- Fix for Boehm GC to detect global vars when running in JIT
    genGcAddRoot ref
    genStore e' (VLocal (ConstantOperand ref)) $> ()

genGlobVarDecl :: VarDef -> Gen' Definition
genGlobVarDecl (TypedVar v t, (ts, _)) = do
    let name = mkName (mangleName (v, ts))
    t' <- genType' t
    pure (GlobalDefinition (simpleGlobVar name t' (LLConst.Undef t')))

-- TODO: Detect when a fun def is nested lambdas, like (define (foo a b) (+ a b)). Now,
--       nested functions wrappers are generated for the currying that handle boilerplate
--       closure capturing, but only the outermost, fully curried function is actually
--       exposed as a variable, and if you apply the function with all arguments, like
--       (foo 1 2), it has to needlessly go through all the wrapping stuff of putting in
--       closures and directly extracting again.
--
--       It would be a serious optimization to handle saturated (i.e., fully applied)
--       calls specially. Just generate an extra, innermost function that takes the params
--       as a tuple, and does no closure-extraction stuff, then generate the currying
--       wrappers around that.
--
--       Look at how Haskell does
--       it. https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/rts/haskell-execution/function-calls. Seems
--       very reasonable. They handle 4 different cases when compiling a call: Unknown
--       function, Known function - saturated call, Known function - too few arguments,
--       and Known function - too many arguments.
--
--       Additional reading: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.134.9317&rep=rep1&type=pdf
genGlobFunDef :: FunDef -> Gen' [Definition]
genGlobFunDef (TypedVar v _, (ts, (p, (body, rt)))) = do
    let name = mangleName (v, ts)
    assign lambdaParentFunc (Just name)
    let fName = mkName (name ++ "_func")
    (f, gs) <- genFunDef (fName, [], p, genTailExpr body *> genType rt)
    pure (GlobalDefinition f : gs)

genTailExpr :: Expr -> Gen ()
genTailExpr = genExpr

genExpr :: TailVal v => Expr -> Gen v
genExpr expr = do
    case expr of
        Lit c -> propagate =<< genConst c
        Var (_, x) -> propagate =<< lookupVar x
        App f as -> genApp f as
        If p c a -> genExpr p >>= \p' -> genCondBr p' (genExpr c) (genExpr a)
        Fun (p, b) -> genExprLambda p b >>= propagate
        Let d b -> genLet d b
        Match e cs -> genMatch e cs
        Ction c -> propagate =<< genCtion c
        Sizeof t ->
            propagate
                =<< (VLocal . litI64 . fromIntegral)
                <$> ((lift . sizeof) =<< genType t)
        Absurd t -> propagate =<< fmap (VLocal . undef) (genType t)

genExprLambda :: TypedVar -> (Expr, Ast.Type) -> Gen Val
genExprLambda p (b, bt) = do
    fvXs <- view localEnv <&> \locals ->
        Set.toList (Set.intersection (Set.delete p (freeVars b)) (Map.keysSet locals))
    bt' <- genType bt
    genLambda fvXs p (genTailExpr b, bt')

genConst :: Ast.Const -> Gen Val
genConst = \case
    Int n -> pure (VLocal (litI64 n))
    F64 x -> pure (VLocal (litF64 x))
    Str s -> genStrLit s

genStrLit :: String -> Gen Val
genStrLit s = do
    var <- newName "strlit"
    scribe outStrings [(var, s)]
    pure $ VVar $ ConstantOperand (LLConst.GlobalReference (LLType.ptr typeStr) var)

class TailVal v where
    propagate :: Val -> Gen v
    app' :: Val -> Val -> Gen v
    converge :: Gen v -> [(Name, Gen v)] -> Gen v

instance TailVal Val where
    propagate = pure
    app' = app (Just NoTail)
    converge default' cs = do
        nextL <- newName "next"
        v <- liftA2 (,) (getLocal =<< default') (use currentBlockLabel)
        let genCase (l, mv) = do
                commitToNewBlock (br nextL) l
                liftA2 (,) (getLocal =<< mv) (use currentBlockLabel)
        vs <- mapM genCase cs
        commitToNewBlock (br nextL) nextL
        fmap VLocal (emitAnonReg (phi (v : vs)))

instance TailVal () where
    propagate v = commitFinalFuncBlock . ret =<< getLocal v
    app' f e = propagate =<< app (Just Tail) f e
    converge default' cs = do
        () <- default'
        forM_ cs $ \(l, gen) -> assign currentBlockLabel l *> gen

genApp :: TailVal v => Expr -> [Expr] -> Gen v
genApp fe aes = case fe of
    Var (Virt, x) -> propagate =<< genAppBuiltinVirtual x =<< mapM genExpr aes
    _ -> do
        f <- genExpr fe
        as <- mapM genExpr (init aes)
        closure <- foldlM app' f as
        arg <- genExpr (last aes)
        app' closure arg

genCondBr :: TailVal v => Val -> Gen v -> Gen v -> Gen v
genCondBr predV genConseq genAlt = do
    predV' <- emitAnonReg . flip trunc i1 =<< getLocal predV
    conseqL <- newName "consequent"
    altL <- newName "alternative"
    commitToNewBlock (condbr predV' conseqL altL) conseqL
    converge genConseq [(altL, genAlt)]

genLet :: TailVal v => Def -> Expr -> Gen v
genLet def body = case def of
    VarDef (lhs, (_, rhs)) -> genExpr rhs >>= \rhs' -> withVal lhs rhs' (genExpr body)
    RecDefs ds -> do
        (binds, cs) <- fmap unzip $ forM ds $ \case
            (lhs, (_, (p, (fb, fbt)))) -> do
                fvXs <- view localEnv <&> \locals ->
                    let locals' = Set.insert lhs (Map.keysSet locals)
                    in  Set.toList (Set.intersection (Set.delete p (freeVars fb)) locals')
                tcaptures <- fmap typeStruct (mapM (\(TypedVar _ t) -> genType t) fvXs)
                captures <- genHeapAllocGeneric tcaptures
                fbt' <- genType fbt
                lam <- genLambda' p (genTailExpr fb, fbt') (VLocal captures) fvXs
                pure ((lhs, lam), (captures, fvXs))
        withVals binds $ do
            forM_ cs (uncurry populateCaptures)
            (genExpr body)

genMatch :: TailVal v => Expr -> DecisionTree -> Gen v
genMatch m dt = genDecisionTree dt . newSelections =<< genExpr m

genDecisionTree :: TailVal v => DecisionTree -> Selections Val -> Gen v
genDecisionTree = \case
    Ast.DLeaf l -> genDecisionLeaf l
    Ast.DSwitch selector cs def -> genDecisionSwitchIx selector cs def
    Ast.DSwitchStr selector cs def -> genDecisionSwitchStr selector cs def
  where
    genDecisionLeaf (bs, e) selections = do
        bs' <- selectVarBindings selections bs
        withVals bs' (genExpr e)
    genDecisionSwitchIx selector cs def selections = do
        let (variantIxs, variantDts) = unzip (Map.toAscList cs)
        (m, selections') <- select selector selections
        mVariantIx <- getLocal =<< case typeOf m of
            IntegerType _ -> pure m
            _ -> genIndexStruct m [0]
        let ixBits = getIntBitWidth (typeOf mVariantIx)
        let litIxInt = LLConst.Int ixBits
        variantLs <- mapM (newName . (++ "_") . ("variant_" ++) . show) variantIxs
        defaultL <- newName "default"
        let dests' = zip (map litIxInt variantIxs) variantLs
        commitToNewBlock (switch mVariantIx defaultL dests') defaultL
        converge (genDecisionTree def selections')
                 (zip variantLs (map (flip genDecisionTree selections') variantDts))
    genDecisionSwitchStr selector cs def selections = do
        (matchee, selections') <- select selector selections
        let cs' = Map.toAscList cs
        let genCase (s, dt) next = do
                s' <- genStrLit s
                isMatch <- genStrEq matchee s'
                -- Do some wrapping to preserve effect order
                pure $ genCondBr isMatch (genDecisionTree dt selections') next
        join (foldrM genCase (genDecisionTree def selections') cs')

genCtion :: Ast.Ction -> Gen Val
genCtion (i, span', dataType, as) = do
    lookupEnum dataType & lift >>= \case
        Just 0 -> pure (VLocal litUnit)
        Just w -> pure (VLocal (ConstantOperand (LLConst.Int w i)))
        Nothing -> do
            as' <- mapM genExpr as -- can have side effects, so generate even if zero size
            let tgeneric = genDatatypeRef dataType
            size <- sizeof tgeneric
            if size == 0
                then pure (VLocal (undef tgeneric))
                else do
                    let tagged = maybe
                            as'
                            ((: as') . VLocal . ConstantOperand . flip LLConst.Int i)
                            (tagBitWidth span')
                    let t = typeStruct (map typeOf tagged)
                    pGeneric <- emitReg "ction_ptr_nominal" (alloca tgeneric)
                    p <- emitReg "ction_ptr_structural" (bitcast pGeneric (LLType.ptr t))
                    genStructInPtr p tagged
                    pure (VVar pGeneric)

genStrEq :: Val -> Val -> Gen Val
genStrEq s1 s2 =
    fmap VLocal . emitAnonReg =<< callBuiltin "carth_str_eq" =<< mapM getLocal [s1, s2]
