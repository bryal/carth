{-# LANGUAGE TemplateHaskell, DataKinds, InstanceSigs, ScopedTypeVariables, RankNTypes #-}

-- | Lower a monomorphic AST to our Low IR
--
--   Generally, structs are kept on the stack in Low IR, even small ones. This way, we don't have
--   to add additional insert- and extract-element operations to our IR - struct member indexing
--   and load/store will be enough. We assume that the machine code generator (e.g. LLVM, GCC) will
--   put things in registers and such for us as needed. In some moments we do have to load structs
--   into locals though, e.g. when a small struct is an argument to a function call.

module Back.Lower (lower) where

import qualified Codec.Binary.UTF8.String as UTF8.String
import Control.Arrow
import Control.Monad
import Control.Monad.RWS
import Data.Bifunctor (bimap)
import Data.Bitraversable
import Data.Char
import Data.Either
import Data.Foldable
import Data.Functor
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as Vec
import Data.Word
import Lens.Micro.Platform (makeLenses, modifying, use, view, (<<.=), to)
import Back.Low (typeof, paramName, paramType, addParamName, dropParamName, Sized (..), fromSized, sizedMaybe, mapSized, sized, catSized, OutParam (..), outParamLocal, MemberName (..), MemberIx, Union (..), pointee, asTConst)
import qualified Back.Low as Low
import Front.Monomorphize as Ast
import Front.Monomorphic as Ast
import qualified Front.TypeAst as Ast hiding (TConst)
import Misc
import Sizeof hiding (sizeof)
import FreeVars

data TypeEnv = TypeEnv
    { _tids :: Map Ast.TConst (Sized Low.TypeId)
    , _tdefs :: Seq Low.TypeDef
    , _tdefIds :: Map Low.TypeDef Low.TypeId -- ^ Use to deduplicate equivalent type defs
    , _datas :: Ast.Datas -- ^ Available data type definitions from previous stages
    }
makeLenses ''TypeEnv

data St = St
    { _strLits :: Map String Low.GlobalId
    , _allocs :: [(Low.LocalId, Low.Type)]
    , _localNames :: Seq String
    , _globalNames :: Seq String
    , _tenv :: TypeEnv
    }
makeLenses ''St

data Env = Env
    { _localEnv :: Map TypedVar Low.Operand
    , _globalEnv :: Map TypedVar Low.Global
    -- | Each extern function comes coupled with a wrapper function that accepts & discards a
    --   closure captures parameter.
    , _externEnv :: Map TypedVar (Low.Extern, Low.Global)
    , _selfFun :: Maybe (TypedVar, Low.Operand, Low.Global)
    }
makeLenses ''Env

data Out = Out
    { _outFunDefs :: [Low.FunDef]
    , _outConstDefs :: [(Low.GlobalId, Low.Type, Low.Const)]
    }
makeLenses ''Out

instance Semigroup Out where
    (<>) (Out a1 b1) (Out a2 b2) = Out (a1 ++ a2) (b1 ++ b2)
instance Monoid Out where
    mempty = Out [] []

type Lower = RWS Env Out St

class Destination d where
    type DestTerm d

    -- | Take an object which is located /here/ and put it in the destination. A struct is located
    --   /here/ if it's here directly, and not behind a pointer (e.g., on the stack).
    sizedToDest :: d -> Sized Low.Expr -> Lower (Low.Block (DestTerm d))

    -- | Take a struct which is located somewhere indirectly behind a pointer, and put it in the
    --   destination. In practice, this means loading it before passing it along to `toDest`,
    --   unless the destination is `Anywhere`, in which case this is the identity function.
    indirectToDest :: d -> Low.Expr -> Lower (Low.Block (DestTerm d))

    branchToDest :: d -> Low.Branch (DestTerm d) -> Low.Block (DestTerm d)

    allocationAtDest :: d -> Maybe String -> Low.Type -> Lower (Low.Operand, DestTerm d)

toDest :: Destination d => d -> Low.Expr -> Lower (Low.Block (DestTerm d))
toDest dest = sizedToDest dest . Sized

newtype There = There Low.Operand deriving Show
instance Destination There where
    type DestTerm There = ()

    sizedToDest (There a) = \case
        ZeroSized -> ice "Lower.sizedToDest: ZeroSized to There"
        Sized e -> bindrBlockM' (emit e) $ \v -> pure (Low.Block [Low.Store v a] ())

    indirectToDest d e = loadE e `bindrBlockM'` toDest d

    branchToDest (There _) br = Low.Block [Low.SBranch br] ()

    allocationAtDest (There addr) _name t = if typeof addr /= Low.TPtr t
        then
            ice
            $ "Lower.allocationAtDest There: Type of destination, `"
            ++ show (typeof addr)
            ++ "`, differs from type of desired allocation, `"
            ++ show (Low.TPtr t)
            ++ "`"
        else pure (addr, ())

newtype ThereSized = ThereSized Low.Operand deriving Show
instance Destination ThereSized where
    type DestTerm ThereSized = Sized ()

    sizedToDest (ThereSized a) = \case
        ZeroSized -> pure (Low.Block [] ZeroSized)
        Sized e -> mapTerm Sized <$> toDest (There a) e

    indirectToDest (ThereSized a) = fmap (mapTerm Sized) . indirectToDest (There a)

    branchToDest (ThereSized _) br =
        Low.Block [Low.SBranch (mapBranchTerm (const ()) br)] (branchGetSomeTerm br)

    allocationAtDest (ThereSized addr) name t =
        second Sized <$> allocationAtDest (There addr) name t

-- Directly here, which means structs are not kept on the stack, but loaded to locals.
data Here = Here
    deriving Show
instance Destination Here where
    type DestTerm Here = Low.Expr

    sizedToDest Here = \case
        ZeroSized -> ice "Lower.toDest: ZeroSized to Here"
        Sized e -> pure . Low.Block [] $ e

    indirectToDest Here = loadE

    branchToDest Here br =
        Low.Block [] (Low.Expr (Low.EBranch br) (typeof (branchGetSomeTerm br)))

    allocationAtDest Here name t =
        stackAlloc name t <&> \addr -> (addr, Low.Expr (Low.Load addr) t)

-- Directly here, which means structs are not kept on the stack, but loaded to locals.
data HereSized = HereSized
    deriving Show
instance Destination HereSized where
    type DestTerm HereSized = Sized Low.Expr

    sizedToDest HereSized = pure . Low.Block []

    indirectToDest HereSized = fmap (mapTerm Sized) . loadE

    branchToDest HereSized br = case branchGetSomeTerm br of
        Sized _ -> mapTerm Sized $ branchToDest Here (mapBranchTerm fromSized br)
        ZeroSized -> Low.Block [Low.SBranch (mapBranchTerm (const ()) br)] ZeroSized

    allocationAtDest HereSized = fmap (second Sized) .* allocationAtDest Here

data Nowhere = Nowhere
    deriving Show
instance Destination Nowhere where
    type DestTerm Nowhere = ()

    sizedToDest Nowhere = \case
        ZeroSized -> pure $ Low.Block [] ()
        Sized _ -> ice "Lower.sizedToDest: Sized to Nowhere"

    indirectToDest Nowhere _ = ice "Lower.indirectToDest: expression to Nowhere"

    branchToDest Nowhere br = Low.Block [Low.SBranch br] ()

    allocationAtDest Nowhere _ _ = ice "Lower.allocationAtDest: allocation at Nowhere"

-- | "Anywhere" => "Wherever is appropriate for the type"
--
--   Structs are kept on the stack, other types are kept in locals, and zero-sized types are
--   allowed.
data Anywhere = Anywhere
    deriving Show
instance Destination Anywhere where
    type DestTerm Anywhere = Sized Low.Expr

    sizedToDest Anywhere = \case
        ZeroSized -> pure (Low.Block [] ZeroSized)
        Sized e -> mapTerm Sized <$> addIndirectionE e

    indirectToDest Anywhere e = pure (Low.Block [] (Sized e))

    -- Assumes that the input branch truly terminates with a result of DestTerm Anywhere
    branchToDest Anywhere = branchToDest HereSized

    allocationAtDest Anywhere =
        fmap (\ptr -> (ptr, Sized $ Low.Expr (Low.EOperand ptr) (typeof ptr))) .* stackAlloc

-- | Destination is a function argument, or some equivalent location. This means that structs are
--   kept on stack iff the ABI specifies that they are to be passed behind a pointer.
data Arg = Arg
    deriving Show
instance Destination Arg where
    type DestTerm Arg = Sized Low.Expr

    sizedToDest Arg = \case
        ZeroSized -> pure (Low.Block [] ZeroSized)
        Sized e -> do
            passByRef (typeof e) >>= \case
                False -> pure (Low.Block [] (Sized e))
                True -> do
                    Low.Block stms1 v <- emit e
                    (ptr, retVal) <- allocationAtDest Arg Nothing (typeof v)
                    let stm2 = Low.Store v ptr
                    pure $ Low.Block (stms1 ++ [stm2]) retVal

    indirectToDest Arg e = passByRef (pointee (typeof e)) >>= \case
        True -> pure (Low.Block [] (Sized e))
        False -> mapTerm Sized <$> loadE e

    -- Assumes that the input branch truly terminates with a result of DestTerm Anywhere
    branchToDest Arg = branchToDest HereSized

    allocationAtDest Arg name t = do
        ptr <- stackAlloc name t
        fmap ((ptr, ) . Sized) $ passByRef t <&> \case
            True -> Low.mkEOperand ptr
            False -> Low.Expr (Low.Load ptr) t

lower :: Bool -> Program -> Low.Program
lower noGC (Program (Topo defs) datas externs) =
    let
        externNames = map fst externs
        (gfunDefs, gvarDefs) = partitionGlobDefs
        (funLhss, funRhss) = unzip gfunDefs
        (varLhss, varRhss) = unzip gvarDefs
        (((externs', externWrappers), varDecls', mainId), st, out) = runLower datas $ do
            externs'' <- lowerExterns
            funIds <- mapM (newGName . tvName) funLhss
            varIds <- mapM (newGName . tvName . fst) gvarDefs
            varDecls <- zipWithM declareGlobVar varLhss varIds
            withExterns externs''
                . withGlobFuns (zip funLhss funIds)
                . withGlobVars (zip varLhss varDecls)
                $ do
                      fs' <- zipWith3M (lowerFunDef [] . Just) funLhss funIds funRhss
                      init <- defineInit (zip varDecls varRhss)
                      scribe outFunDefs (fs' ++ [init])
                      mainId' <- view (globalEnv . to (Map.! TypedVar "main" Ast.mainType))
                      pure
                          ( unzip (map snd externs'')
                          , mapMaybe (fmap (uncurry Low.GlobVarDecl) . sizedMaybe) varDecls
                          , mainId'
                          )
        names = Vec.fromList
            $ resolveNameConflicts ("main" : externNames) (toList (view globalNames st))
        fs = view outFunDefs out
        cs = map (\(gid, t, c) -> Low.GlobConstDef gid t c) (view outConstDefs out)
        tdefs' =
            Vec.fromList . uncurry zip . first (resolveNameConflicts []) . unzip . toList $ view
                (tenv . tdefs)
                st
    in
        Low.Program (externWrappers ++ fs) externs' (cs ++ varDecls') tdefs' names mainId
  where
    runLower datas la = runRWS la initEnv initSt
      where
        initSt = St
            { _strLits = Map.empty
            , _allocs = []
            , _localNames = Seq.empty
            , _globalNames = builtinNames
            , _tenv = TypeEnv { _tids = Map.empty
                              , _tdefs = Seq.fromList builtinTypeDefs
                              , _tdefIds = Map.fromList (zip builtinTypeDefs [0 ..])
                              , _datas = datas
                              }
            }
        initEnv = Env { _localEnv = Map.empty
                      , _globalEnv = Map.empty
                      , _externEnv = Map.empty
                      , _selfFun = Nothing
                      }

    builtinNames :: Seq String
    builtinNames = Seq.fromList ["carth_init"]

    initName = fromIntegral (fromJust (Seq.elemIndexL "carth_init" builtinNames))

    partitionGlobDefs :: ([(TypedVar, Fun)], [(TypedVar, Expr)])
    partitionGlobDefs =
        let defs' = defs >>= \case
                VarDef d -> [d]
                RecDefs ds -> map (second (second Fun)) ds
        in  flip partitionWith defs' $ \(lhs, (_inst, e)) -> case e of
                Fun f -> Left (lhs, f)
                _ -> Right (lhs, e)

    -- In addition to lowering the extern declaration directly, also generates a wrapping function
    -- that accepts & discards a closure captures parameter.
    lowerExterns :: Lower [(TypedVar, (Low.ExternDecl, Low.FunDef))]
    lowerExterns = forM externs $ \case
        (name, t@(TFun pts rt)) -> do
            (outParam, ret) <- toRet (pure ()) =<< lowerType rt
            ps <- lowerParamTypes pts
            let decl = Low.ExternDecl name outParam ps ret
                operand = Low.OExtern (externDeclToExtern decl)
            wrapperName <- newGName (name ++ "_wrapper")
            let capturesParam = Low.ByVal () Low.VoidPtr
                wrapperOutParam = fmap (\out -> out { outParamName = 0 }) outParam
                wrapperParams = zipWith Low.addParamName
                                        [if isJust outParam then 1 else 0 ..]
                                        (capturesParam : ps)
                wrapperParamLocals = map (Low.OLocal . paramLocal) wrapperParams
                callExternWithoutCaptures = case ret of
                    Low.RetVoid -> Low.Block
                        [ Low.VoidCall operand
                                       (fmap (Low.OLocal . outParamLocal) wrapperOutParam)
                                       (tail wrapperParamLocals)
                        ]
                        Low.TRetVoid
                    Low.RetVal t -> Low.Block [] . Low.TRetVal $ Low.Expr
                        (Low.Call operand (tail wrapperParamLocals))
                        t
                varNames =
                    (if isJust outParam then ("sret" :) else id)
                        $ take (length wrapperParams)
                        $ "_captures"
                        : map (\i -> "x" ++ show i) [0 :: Word ..]
                wrapper = Low.FunDef wrapperName
                                     wrapperOutParam
                                     wrapperParams
                                     ret
                                     callExternWithoutCaptures
                                     []
                                     (Vec.fromList varNames)
            pure (TypedVar name t, (decl, wrapper))
        (name, t) -> nyi $ "lower: Non-function externs: " ++ name ++ ", " ++ show t

    declareGlobVar :: TypedVar -> Low.GlobalId -> Lower (Sized (Low.GlobalId, Low.Type))
    declareGlobVar tv gid = mapSized (gid, ) <$> lowerType (tvType tv)

    withExterns :: [(TypedVar, (Low.ExternDecl, Low.FunDef))] -> Lower a -> Lower a
    withExterns es = locallySet
        externEnv
        (Map.fromList (map (second (bimap externDeclToExtern funDefGlobal)) es))

    externDeclToExtern (Low.ExternDecl x out ps r) = Low.Extern x out ps r

    withGlobFuns :: [(TypedVar, Low.GlobalId)] -> Lower a -> Lower a
    withGlobFuns fs ma = do
        fs' <- forM fs $ \(tv, gid) ->
            (tv, ) . Low.Global gid . uncurry3 Low.TFun . asTClosure . fromSized <$> lowerType
                (tvType tv)
        augment globalEnv (Map.fromList fs') ma

    withGlobVars :: [(TypedVar, Sized (Low.GlobalId, Low.Type))] -> Lower a -> Lower a
    withGlobVars vs = augment globalEnv . Map.fromList $ mapMaybe
        (\(tv, g) -> fmap ((tv, ) . uncurry Low.Global . second Low.TPtr) (sizedMaybe g))
        vs

    defineInit :: [(Sized (Low.GlobalId, Low.Type), Expr)] -> Lower Low.FunDef
    defineInit varDefs = do
        block <- mapTerm (const Low.TRetVoid) . catBlocks <$> mapM defineGlobVar varDefs
        localNames' <-
            Vec.fromList . resolveNameConflicts [] . toList <$> replaceLocalNames Seq.empty
        allocs' <- replaceAllocs []
        pure $ Low.FunDef initName Nothing [] Low.RetVoid block allocs' localNames'

    defineGlobVar :: (Sized (Low.GlobalId, Low.Type), Expr) -> Lower (Low.Block ())
    defineGlobVar (g, e) = case g of
        Sized (gid, t) -> do
            let ref = Low.Global gid (Low.TPtr t)
            -- Fix for Boehm GC to detect global vars when running in JIT
            blk <- gcAddRoot ref
            blk `thenBlockM` lowerExpr (There (Low.OGlobal ref)) e
        ZeroSized -> lowerExpr Nowhere e
      where
        -- | Must be used on globals when running in JIT, as Boehm GC only detects global var roots
        --   when it can scan some segment in the ELF.
        gcAddRoot :: Low.Global -> Lower (Low.Block ())
        gcAddRoot globRef = if noGC
            then pure (Low.Block [] ())
            else do
                let p0 = Low.CBitcast (Low.CGlobal globRef) (Low.TPtr (Low.TNat 8))
                    ptrSize = 8
                    p1 = Low.CPtrIndex p0 ptrSize
                stm <- fromRight (ice "GC_add_roots, not a void call")
                    <$> callBuiltin "GC_add_roots" Nothing [Low.OConst p0, Low.OConst p1]
                pure (Low.Block [stm] ())

lowerFunDef :: [TypedVar] -> Maybe TypedVar -> Low.GlobalId -> Fun -> Lower Low.FunDef
lowerFunDef freeLocals lhs name (ps, (body, rt)) = locallySet localEnv Map.empty $ do
        -- Gotta remember these for when we return to whichever scope we came from
    oldLocalNames <- replaceLocalNames Seq.empty
    oldAllocs <- replaceAllocs []
    (outParam, ret) <- toRet (newLName "sret") =<< lowerType rt
    capturesName <- newLName "captures"
    let capturesParam = Low.ByVal capturesName Low.VoidPtr
    Low.Block capturesStms capturesBinds <- unpackCaptures capturesName freeLocals
    (ps', params) <-
        unzip
        . catMaybes
        <$> mapM (\p@(TypedVar x t) -> fmap (p, ) <$> (sizedToParam x =<< lowerType t)) ps
    let selfFun' =
            let tselfFun = Low.TFun (fmap (\out -> out { outParamName = () }) outParam)
                                    (dropParamName capturesParam : map dropParamName params)
                                    ret
                selfCaptures = Low.OLocal $ Low.Local capturesName Low.VoidPtr
                selfRef = Low.Global name tselfFun
            in  fmap (, selfCaptures, selfRef) lhs
    -- The outer parameters will be discarded if the function is not tail recursive. In that
    -- case, the inner params and the outer params are the same.
    innerParamIds <- mapM (newLName . paramName) params
    outerParamIds <- mapM (newLName . paramName) params
    let innerParams = zipWith Low.Local innerParamIds (map paramType params)
    let outerParams = zipWith Low.Local outerParamIds (map paramType params)
    -- Lower the body and optimize to loop if the function is tail recursive.
    (outerParamIds, body'') <- locallySet selfFun selfFun' $ do
        (blkBinds, binds) <- fmap (separateTerm . mapTerm (zip ps') . catBlocks)
                                  (mapM (addIndirection . Low.OLocal) innerParams)
        let lowerBody :: Destination d => d -> Expr -> Lower (Low.Block (DestTerm d))
            lowerBody dest body = blkBinds `thenBlockM` lowerExpr dest body
        withVars (capturesBinds ++ binds) $ case (outParam, ret) of
            (Nothing, Low.RetVoid) -> do
                body' <- lowerBody Nowhere body
                pure $ if isTailRec_RetVoid name body'
                    then (outerParamIds, tailCallOpt_RetVoid name outerParams innerParams body')
                    else (innerParamIds, mapTerm (\() -> Low.TRetVoid) body')
            (Nothing, Low.RetVal _rt) -> do
                body' <- lowerBody Here body
                pure $ if isTailRec_RetVal name body'
                    then (outerParamIds, tailCallOpt_RetVal name outerParams innerParams body')
                    else (innerParamIds, mapTerm Low.TRetVal body')
            (Just outParam', Low.RetVoid) -> do
                let outParamOp = Low.OLocal $ outParamLocal outParam'
                body' <- lowerBody (There outParamOp) body
                pure $ if isTailRec_RetVoid name body'
                    then (outerParamIds, tailCallOpt_RetVoid name outerParams innerParams body')
                    else (innerParamIds, mapTerm (\() -> Low.TRetVoid) body')
            (Just _, Low.RetVal _) -> unreachable
    let body''' = Low.Block capturesStms () `thenBlock` body''
    localNames' <-
        Vec.fromList . resolveNameConflicts [] . toList <$> replaceLocalNames oldLocalNames
    allocs' <- replaceAllocs oldAllocs
    let params' = capturesParam : zipWith addParamName outerParamIds params
    pure $ Low.FunDef name outParam params' ret body''' allocs' localNames'
  where
    unpackCaptures :: Low.LocalId -> [TypedVar] -> Lower (Low.Block [(TypedVar, Low.Operand)])
    unpackCaptures capturesName freeVars = do
        ts <- mapM (lowerType . tvType) freeVars
        case sizedMembers ts of
            [] -> pure (Low.Block [] [])
            members -> do
                let capturesGeneric = Low.OLocal $ Low.Local capturesName Low.VoidPtr
                tcaptures <- Low.TConst <$> defineStruct "captures" members
                captures <-
                    let t = Low.TPtr tcaptures
                    in  emitNamed "captures" (Low.Expr (Low.Bitcast capturesGeneric t) t)
                captures `bindrBlockM` \captures' -> catBlocks <$> mapM
                    (\(v@(TypedVar x _), (i, t)) -> mapTerm (v, ) <$> do
                        member <- emitNamed x (Low.Expr (Low.EGetMember i captures') (Low.TPtr t))
                        onStack <- keepOnStack t
                        if onStack then pure member else bindBlockM load member
                    )
                    (zip freeVars members)

    isTailRec_RetVoid self = go
      where
        go (Low.Block stms ()) = case lastMay stms of
            Just (Low.VoidCall (Low.OGlobal (Low.Global other _)) _ _) | other == self -> True
            Just (Low.SBranch br) -> goBranch br
            _ -> False
        goBranch = \case
            Low.BIf _ b1 b2 -> go b1 || go b2
            Low.BSwitch _ cs d -> any (go . snd) cs || go d

    isTailRec_RetVal self = go
      where
        go (Low.Block _ (Low.Expr e _)) = case e of
            Low.Call (Low.OGlobal (Low.Global other _)) _ | other == self -> True
            Low.EBranch br -> goBranch br
            _ -> False
        goBranch = \case
            Low.BIf _ b1 b2 -> go b1 || go b2
            Low.BSwitch _ cs d -> any (go . snd) cs || go d

    tailCallOpt_RetVoid self outerParams innerParams body =
        let loopInner = go body
            loopParams = zip innerParams (map Low.OLocal outerParams)
            loop = Low.Loop loopParams loopInner
        in  Low.Block [Low.SLoop loop] Low.TRetVoid
      where
        goStm = \case
            Low.VoidCall (Low.OGlobal (Low.Global other _)) _out args | other == self ->
                Low.Block [] (Low.Continue (drop (length args - length outerParams) args))
            Low.SBranch br -> goBranch br
            stm -> Low.Block [stm] (Low.Break ())
        goBranch = \case
            Low.BIf pred conseq alt ->
                Low.Block [] . Low.LBranch $ Low.BIf pred (go conseq) (go alt)
            Low.BSwitch matchee cases default' -> Low.Block [] . Low.LBranch $ Low.BSwitch
                matchee
                (map (second go) cases)
                (go default')
        go (Low.Block stms ()) = case unsnoc stms of
            Just (initStms, lastStm) ->
                let termBlock = goStm lastStm in Low.Block initStms () `thenBlock` termBlock
            Nothing -> Low.Block [] (Low.Break ())

    tailCallOpt_RetVal
        :: Low.GlobalId
        -> [Low.Local]
        -> [Low.Local]
        -> Low.Block Low.Expr
        -> Low.Block Low.Terminator
    tailCallOpt_RetVal self outerParams innerParams body@(Low.Block _ (Low.Expr _ t)) =
        let loopInner = go body
            loopParams = zip innerParams (map Low.OLocal outerParams)
            loop = Low.Loop loopParams loopInner
            t = Low.eType (Low.blockTerm body)
        in  Low.Block [] (Low.TRetVal (Low.Expr (Low.ELoop loop) t))
      where
        go (Low.Block stms (Low.Expr lastExpr _)) =
            let termBlock = goExpr lastExpr in Low.Block stms () `thenBlock` termBlock
        goExpr = \case
            Low.Call (Low.OGlobal (Low.Global other _)) args | other == self ->
                Low.Block [] (Low.Continue (tail args))
            Low.EBranch br -> goBranch br
            e -> Low.Block [] (Low.Break (Low.Expr e t))
        goBranch = \case
            Low.BIf pred conseq alt ->
                Low.Block [] . Low.LBranch $ Low.BIf pred (go conseq) (go alt)
            Low.BSwitch matchee cases default' -> Low.Block [] . Low.LBranch $ Low.BSwitch
                matchee
                (map (second go) cases)
                (go default')

resolveNameConflicts :: [String] -> [String] -> [String]
resolveNameConflicts fixedNames names = reverse . snd $ foldl'
    (\(seen, acc) name ->
        let n = fromMaybe (0 :: Word) (Map.lookup name seen)
            (n', name') = incrementUntilUnseen seen n name
        in  (Map.insert name (n' + 1) seen, name' : acc)
    )
    (Map.fromList (zip fixedNames (repeat 1)), [])
    names
  where
    incrementUntilUnseen seen n name =
        let name' = if n == 0 then name else name ++ "_" ++ show n
        in  if Map.member name' seen then incrementUntilUnseen seen (n + 1) name else (n, name')

lowerExpr :: Destination d => d -> Expr -> Lower (Low.Block (DestTerm d))
lowerExpr dest = \case
    Lit c -> lowerConst dest c
    -- TODO: Keep a cache of wrapped virtuals, so as to not generate the same instantiation
    --       twice
    Var Virt f@(TypedVar _ (TFun pts rt)) ->
        let ps = zipWith TypedVar (map ((: []) . chr) [ord 'a' ..]) pts
            as = map (Var NonVirt) ps
        in  lowerLambda dest (ps, (App (Var Virt f) as, rt))
    Var Virt x -> ice $ "lowerExpr of non-function virtual " ++ show x
    Var NonVirt x -> lookupVar dest x
    App f as -> lowerApp dest f as
    If pred conseq alt ->
        lowerExpr Here pred `bindrBlockM'` emitNamed "predicate" `bindrBlockM'` \pred' -> do
            conseq' <- lowerExpr dest conseq
            alt' <- lowerExpr dest alt
            pure . branchToDest dest $ Low.BIf pred' conseq' alt'
    Fun f -> lowerLambda dest f
    Let (VarDef (lhs, (_, rhs))) body -> lowerExpr Anywhere rhs `bindrBlockM'` \case
        ZeroSized -> lowerExpr dest body
        Sized rhs' -> bindrBlockM' (emit rhs') $ \rhs'' -> withVar lhs rhs'' (lowerExpr dest body)
    Let (RecDefs defs) body -> do
        let lhss = Set.fromList $ map fst defs
        Low.Block stms1 (binds, cs) <-
            fmap (mapTerm unzip . catBlocks) . forM defs $ \(lhs, (_, f)) -> do
                (freeLocalVars, (blk, (gcaptures, captures))) <-
                    second separateTerm <$> precaptureFreeLocalVars (Set.delete lhs lhss) f
                name <- newGName (tvName lhs)
                fdef <- lowerFunDef freeLocalVars (Just lhs) name f
                scribe outFunDefs [fdef]
                closure <-
                    bindBlockM (emitNamed "closure" . fromSized)
                        =<< wrapInClosure Anywhere (funDefGlobal fdef) gcaptures
                pure
                    $ blk
                    `thenBlock` mapTerm (\c -> ((lhs, c), (freeLocalVars, captures))) closure
        withVars binds $ do
            Low.Block stms2 () <- catBlocks_ <$> forM cs (uncurry populateCaptures)
            body' <- lowerExpr dest body
            pure (Low.Block (stms1 ++ stms2) () `thenBlock` body')
    Match es dt -> lowerMatch dest es dt
    Ction (variantIx, span, tconst, xs) -> lowerCtion dest variantIx span tconst xs
    Sizeof t ->
        toDest dest
            . Low.mkEOperand
            . Low.OConst
            . litI64
            =<< sized (fmap fromIntegral . sizeof) (pure 0)
            =<< lowerType t
    Absurd _ -> sizedToDest dest ZeroSized
  where
    lowerConst :: Destination d => d -> Const -> Lower (Low.Block (DestTerm d))
    lowerConst dest = \case
        Int n -> toDest dest . Low.mkEOperand . Low.OConst $ Low.CInt
            { Low.intWidth = 64
            , Low.intVal = fromIntegral n
            }
        F64 x -> toDest dest . Low.mkEOperand . Low.OConst $ Low.F64 x
        Str s -> indirectToDest dest . Low.mkEOperand . Low.OGlobal =<< internStr s

    lookupVar :: Destination d => d -> TypedVar -> Lower (Low.Block (DestTerm d))
    lookupVar dest x = do
        lowerType (tvType x) >>= \case
            ZeroSized -> sizedToDest dest ZeroSized
            Sized target -> do
                let toDest' e = if not (Low.isPtr target) && Low.isPtr (typeof e)
                        then indirectToDest dest e
                        else toDest dest e
                maybeLocal <- view (localEnv . to (Map.lookup x))
                maybeGlobal <- view (globalEnv . to (Map.lookup x))
                maybeExtern <- view (externEnv . to (Map.lookup x))
                case (maybeLocal, maybeGlobal, maybeExtern) of
                    (Just l, _, _) -> toDest' (Low.mkEOperand l)
                    (_, Just f@(Low.Global _ Low.TFun{}), _) ->
                        wrapInClosure dest f (Low.OConst (Low.Zero Low.VoidPtr))
                    (_, Just g, _) -> toDest' (Low.mkEOperand (Low.OGlobal g))
                    (_, _, Just (_e, eWrapped)) ->
                        wrapInClosure dest eWrapped (Low.OConst (Low.Zero Low.VoidPtr))
                    _ -> view selfFun >>= \case
                        Just (selfLhs, selfCapts, f) | x == selfLhs ->
                            wrapInClosure dest f selfCapts
                        _ -> ice $ "Lower.lookupVar: undefined var " ++ show x

    lowerLambda :: Destination d => d -> Fun -> Lower (Low.Block (DestTerm d))
    lowerLambda dest f = do
        (freeLocalVars, captures) <- precaptureFreeLocalVars Set.empty f
        let Low.Block stms1 captures' = mapTerm snd captures
        Low.Block stms2 () <- populateCaptures freeLocalVars captures'
        Low.Block stms3 captures'' <- emit
            (Low.Expr (Low.Bitcast captures' Low.VoidPtr) Low.VoidPtr)
        name <- newGName "fun"
        fdef <- lowerFunDef freeLocalVars Nothing name f
        scribe outFunDefs [fdef]
        Low.Block (stms1 ++ stms2 ++ stms3) ()
            `thenBlockM` wrapInClosure dest (funDefGlobal fdef) captures''

lowerApp :: Destination d => d -> Expr -> [Expr] -> Lower (Low.Block (DestTerm d))
lowerApp dest f as = case f of
        -- TODO: Handle this more elegantly. For example by exchanging Ction in Low for a Ctor,
        --       which behaves like a constructor or a function depending on context.
    Fun (params, (Ction (variantIx, span, tconst, xs), _rt)) | map (Var NonVirt) params == xs ->
        lowerCtion dest variantIx span tconst as
    Fun (params, (body, _rt)) -> do -- Beta reduction
        (blk1, as') <- separateTerm <$> lowerEmitExprs Anywhere emitSized as
        let binds = mapMaybe (\(p, a) -> fmap (p, ) (sizedMaybe a)) (zip params as')
        blk1 `thenBlockM` withVars binds (lowerExpr dest body)
    Var Virt f -> lowerAppVirtual dest f as
    Var NonVirt x -> do
        maybeLocal <- view (localEnv . to (Map.lookup x))
        maybeGlobal <- view (globalEnv . to (Map.lookup x))
        maybeExtern <- view (externEnv . to (Map.lookup x))
        maybeSelf <- view selfFun
        (blk1, (captures, fConcrete)) <-
            separateTerm <$> case (maybeLocal, maybeGlobal, maybeExtern, maybeSelf) of
                (Just (Low.OGlobal f@(Low.Global _ Low.TFun{})), _, _, _) ->
                    lowerApplicandGlobal f
                (Just closure, _, _, _) -> lowerApplicandOperand closure
                (_, Just f@(Low.Global _ Low.TFun{}), _, _) -> lowerApplicandGlobal f
                (_, Just closure, _, _) -> lowerApplicandOperand (Low.OGlobal closure)
                (_, _, Just (e, _), _) -> pure (Low.Block [] (Nothing, Low.OExtern e))
                (_, _, _, Just (selfLhs, selfCapts, selfRef)) | x == selfLhs ->
                    pure $ Low.Block [] (Just selfCapts, Low.OGlobal selfRef)
                _ -> ice $ "lowerApp: variable not in any env: " ++ (show x ++ " -- " ++ show as)
        blk1 `thenBlockM` lowerApp' captures fConcrete
    _ -> do
        Low.Block stms (captures, fConcrete) <-
            bindBlockM lowerApplicandOperand
            =<< bindBlockM (emitNamed "closure" . fromSized)
            =<< lowerExpr Anywhere f
        Low.Block stms () `thenBlockM` lowerApp' captures fConcrete
  where
    lowerApp' captures fConcrete = do
        let (outParam, _, ret) = asTFun (typeof fConcrete)
        Low.Block stms1 as' <- lowerArgs as
        let args = maybe id (:) captures as'
        thenBlockM (Low.Block stms1 ()) $ case (outParam, ret) of
            (Just out, Low.RetVoid) -> do
                (ptr, retVal) <- allocationAtDest dest (Just "out") (outParamType out)
                pure $ Low.Block [Low.VoidCall fConcrete (Just ptr) args] retVal
            (Nothing, Low.RetVoid) ->
                Low.Block [Low.VoidCall fConcrete Nothing args] ()
                    `thenBlockM` sizedToDest dest ZeroSized
            (Nothing, Low.RetVal tret) -> toDest dest (Low.Expr (Low.Call fConcrete args) tret)
            (Just _, Low.RetVal _) -> ice "Lower.lowerApp': Both out param and RetVal"
    lowerApplicandOperand closure = do
        Low.Block stms1 captures <- bindBlockM load =<< indexStruct 0 closure
        Low.Block stms2 fGeneric <- bindBlockM load =<< indexStruct 1 closure
        let tfConcrete = uncurry3 Low.TFun $ asTClosure (pointee (typeof closure))
        Low.Block stms3 fConcrete <- emit $ Low.Expr (Low.Bitcast fGeneric tfConcrete) tfConcrete
        pure (Low.Block (stms1 ++ stms2 ++ stms3) (Just captures, fConcrete))
    lowerApplicandGlobal f =
        pure $ Low.Block [] (Just (Low.OConst (Low.Zero Low.VoidPtr)), Low.OGlobal f)

    lowerAppVirtual :: Destination d => d -> TypedVar -> [Expr] -> Lower (Low.Block (DestTerm d))
    lowerAppVirtual dest (TypedVar f tf) as = case f of
        "+" -> arith Low.Add
        "-" -> arith Low.Sub
        "*" -> arith Low.Mul
        "/" -> arith Low.Div
        "rem" -> arith Low.Rem
        "shift-l" -> arith Low.Shl
        "lshift-r" -> arith Low.LShr
        "ashift-r" -> arith Low.AShr
        "bit-and" -> arith Low.BAnd
        "bit-or" -> arith Low.BOr
        "bit-xor" -> arith Low.BXor
        "=" -> rel Low.Eq
        "/=" -> rel Low.Ne
        ">" -> rel Low.Gt
        ">=" -> rel Low.GtEq
        "<" -> rel Low.Lt
        "<=" -> rel Low.LtEq
        "transmute" -> case (tf, as) of
            (TFun [ta] tr, [a]) -> lowerType tr >>= \case
                ZeroSized -> sizedToDest dest ZeroSized
                Sized tr' -> do
                    ta' <- fromSized <$> lowerType ta
                    stackCast_a <- keepOnStack ta'
                    stackCast_r <- keepOnStack tr'
                    if
                        | ta' == tr' -> lowerExpr dest a
                        | stackCast_a || stackCast_r -> do
                            (ptrTo, retVal) <- allocationAtDest dest Nothing tr'
                            Low.Block stms1 ptrFrom <- emit
                                $ Low.Expr (Low.Bitcast ptrTo (Low.TPtr tr')) (Low.TPtr tr')
                            Low.Block stms2 () <- lowerExpr (There ptrFrom) a
                            pure (Low.Block (stms1 ++ stms2) retVal)
                        | otherwise -> do
                            a' <- bindBlockM emit =<< lowerExpr Here a
                            a' `bindrBlockM` \a'' ->
                                toDest dest (Low.Expr (Low.Bitcast a'' tr') tr')
            _ -> err
        "cast" -> case (tf, as) of
            (TFun [ta] tr, [a]) | (isInt ta || isFloat ta) && (isInt tr || isFloat tr) -> do
                tr' <- fromSized <$> lowerType tr
                (blk1, a') <- separateTerm <$> (bindBlockM emit =<< lowerExpr Here a)
                blk2 <- toDest dest (Low.Expr (Low.Cast a' tr') tr')
                pure (blk1 `thenBlock` blk2)
            _ -> err
        "deref" -> case as of
            [a] -> bindrBlockM' (bindBlockM emit =<< lowerExpr Here a)
                $ \a' -> toDest dest (Low.Expr (Low.Load a') (pointee (typeof a')))
            _ -> err
        "store" -> bindrBlockM' (lowerEmitExprs Here emit as) $ \case
            [val, dst] ->
                Low.Block [Low.Store val dst] () `thenBlockM` toDest dest (Low.mkEOperand dst)
            _ -> err
        _ -> ice $ "lowerAppVirtual: no builtin virtual function: " ++ f
      where
        arith op = lowerArgs as >>= bindBlockM
            (\case
                [a, b] -> toDest dest (Low.Expr (op a b) (typeof a))
                _ -> err
            )
        rel op = lowerArgs as >>= bindBlockM
            (\case
                [a, b] -> toDest dest . Low.Expr (op a b) =<< typeBool
                _ -> err
            )
        isInt = \case
            Ast.TPrim (TInt _) -> True
            Ast.TPrim TIntSize -> True
            Ast.TPrim (TNat _) -> True
            Ast.TPrim TNatSize -> True
            _ -> False
        isFloat = \case
            Ast.TPrim TF32 -> True
            Ast.TPrim TF64 -> True
            _ -> False
        err :: e
        err = ice $ "lowerAppVirtual: " ++ show (TypedVar f tf) ++ " of " ++ show as

        typeBool :: Lower Low.Type
        typeBool = fromSized <$> lowerType (TConst ("Bool", []))

wrapInClosure :: Destination d => d -> Low.Global -> Low.Operand -> Lower (Low.Block (DestTerm d))
wrapInClosure dest f@(Low.Global _ t) captures = do
    fGeneric <- emit (Low.Expr (Low.Bitcast (Low.OGlobal f) Low.VoidPtr) Low.VoidPtr)
    (ptr, x) <- allocationAtDest dest (Just "closure") $ uncurry3 Low.TClosure (asTFun t)
    bindrBlockM fGeneric
        $ \fGeneric' -> populateStruct [captures, fGeneric'] ptr <&> mapTerm (const x)

populateStruct :: [Low.Operand] -> Low.Operand -> Lower (Low.Block ())
populateStruct vs dst = foldrM
    (\(i, v) blkRest -> do
        (blk1, member) <- separateTerm <$> indexStruct i dst
        let blk2 = Low.Block [Low.Store v member] ()
        pure $ blk1 `thenBlock` blk2 `thenBlock` blkRest
    )
    (Low.Block [] ())
    (zip [0 ..] vs)

lowerExprsInStruct :: [(MemberName, Expr)] -> Low.Operand -> Lower (Low.Block ())
lowerExprsInStruct es ptr = do
    blks <- forM es $ \(memberName, e) -> bindrBlockM' (lookupStruct memberName ptr) $ \case
        ZeroSized -> lowerExpr Nowhere e
        Sized subPtr -> lowerExpr (There subPtr) e
    pure $ catBlocks_ blks

-- | Returns the list of free variables to capture, and the heap allocated captures struct, both
--   the generic void-pointer, and a pointer to the concrete captures struct.
precaptureFreeLocalVars
    :: Set TypedVar -> Fun -> Lower ([TypedVar], Low.Block (Low.Operand, Low.Operand))
precaptureFreeLocalVars extraLocals (params, (body, _)) = do
    let params' = Set.fromList params
    locals <- Map.keysSet <$> view localEnv
    self <- maybe Set.empty (\(lhs, _, _) -> Set.singleton lhs) <$> view selfFun
    let freeLocals = Set.toList $ Set.intersection (Set.difference (freeVars body) params')
                                                   (Set.unions [extraLocals, self, locals])
    (freeLocals, ) <$> if null freeLocals
        then
            let captures = Low.OConst (Low.Zero Low.VoidPtr)
            in  pure (Low.Block [] (captures, captures))
        else do
            t <-
                fmap Low.TConst
                . defineStruct "captures"
                . sizedMembers
                =<< mapM (lowerType . tvType) freeLocals
            capturesSize <- sizeof t
            (blk1, generic) <- fmap separateTerm . emitNamed "captures" =<< gcAlloc
                (Low.OConst (litI64 (fromIntegral capturesSize)))
            (blk2, captures) <- separateTerm <$> emitNamed
                "captures"
                (Low.Expr (Low.Bitcast generic (Low.TPtr t)) (Low.TPtr t))
            pure (blk1 `thenBlock` blk2 `thenBlock` Low.Block [] (generic, captures))

gcAlloc :: Low.Operand -> Lower Low.Expr
gcAlloc size = fromLeft (ice "gcAlloc: (GC_)malloc was a void call")
    <$> callBuiltin "GC_malloc" Nothing [size]

populateCaptures :: [TypedVar] -> Low.Operand -> Lower (Low.Block ())
populateCaptures freeLocals captures = do
    vs <- mapTerm catSized <$> lowerEmitExprs HereSized emitSized (map (Var NonVirt) freeLocals)
    vs `bindrBlockM` \xs -> populateStruct xs captures

litI64 :: Integer -> Low.Const
litI64 n = Low.CInt { Low.intWidth = 64, Low.intVal = n }

internStr :: String -> Lower Low.Global
internStr s = do
    tStr <- fromSized <$> lowerType Ast.tStr
    tArray <- fromSized <$> lowerType (Ast.tArray (TPrim (TNat 8)))
    use (strLits . to (Map.lookup s)) >>= \case
        Just name -> pure (Low.Global name (Low.TPtr tStr))
        Nothing -> do
            nameInner <- newGName "str_inner"
            name <- newGName "str"
            let bytes = UTF8.String.encode s
                len = length bytes
                tInner = Low.TArray (Low.TNat 8) (fromIntegral len)
                inner = Low.Global nameInner (Low.TPtr tInner)
                ptrBytes = Low.CBitcast (Low.CGlobal inner) (Low.TPtr (Low.TNat 8))
                array = Low.CStruct tArray [ptrBytes, Low.CNat 64 (fromIntegral len)]
                strRhs = Low.CStruct tStr [array]
            scribe outConstDefs [(nameInner, tInner, Low.CharArray bytes), (name, tStr, strRhs)]
            modifying strLits (Map.insert s name)
            pure (Low.Global name (Low.TPtr tStr))

lowerStrEq :: Low.Operand -> Low.Operand -> Lower Low.Expr
lowerStrEq s1 s2 =
    fromLeft (ice "lowerStrEq: str-eq was a void call") <$> callBuiltin "str-eq" Nothing [s1, s2]

callBuiltin
    :: String -> Maybe Low.Operand -> [Low.Operand] -> Lower (Either Low.Expr Low.Statement)
callBuiltin fname out args = do
    es <- view externEnv
    let f = Low.OExtern . fst $ es Map.! TypedVar fname (Ast.builtinExterns Map.! fname)
    pure $ case returnee (typeof f) of
        Low.RetVal t -> Left (Low.Expr (Low.Call f args) t)
        Low.RetVoid -> Right (Low.VoidCall f out args)

lowerMatch
    :: forall d . Destination d => d -> [Expr] -> DecisionTree -> Lower (Low.Block (DestTerm d))
lowerMatch dest matchees decisionTree = do
    Low.Block stms1 ms <- catBlocks <$> mapM lowerMatchee matchees
    Low.Block stms2 result <- lowerDecisionTree (topSelections ms) decisionTree
    pure (Low.Block (stms1 ++ stms2) result)
  where
    lowerMatchee m = lowerExpr Anywhere m `bindrBlockM'` \case
        ZeroSized -> pure $ Low.Block [] ZeroSized
        Sized e -> mapTerm Sized <$> emitNamed "matchee" e

    topSelections :: [Sized Low.Operand] -> Map Access (Sized Low.Operand)
    topSelections xs = Map.fromList $ zipWith (\i x -> (TopSel i, x)) [0 ..] xs

    lowerDecisionTree
        :: Map Access (Sized Low.Operand) -> DecisionTree -> Lower (Low.Block (DestTerm d))
    lowerDecisionTree selections = \case
        DLeaf (bs, e) -> selectVarBindings selections bs
            `bindrBlockM'` \vars' -> withVars vars' (lowerExpr dest e)
        DSwitch span access cases default_ -> do
            ((blk, m), selections') <- first separateTerm <$> select access selections
            blk `thenBlockM` case m of
                -- Somewhat bad manners of previous stages to pass something like this, but
                -- type-wise it's legal, so we ought to handle it.
                ZeroSized | Map.null cases -> lowerDecisionTree selections' default_
                ZeroSized ->
                    ice
                        $ "Lower.lowerDecisionTree: matchee zero sized, but there are multiple cases, "
                        ++ (show cases ++ ", " ++ show default_)
                Sized m' -> do
                    (blk', tag) <- separateTerm <$> case typeof m' of
                        -- Either a pointer to a struct, representing a tagged union
                        Low.TPtr (Low.TConst _) -> bindBlockM' load (indexStruct 0 m')
                        -- or an enum, which, as an integer, is its own "tag"
                        _ -> pure (Low.Block [] m')
                    cases' <- mapM
                        (bimapM (pure . lowerTag span) (lowerDecisionTree selections'))
                        (Map.toAscList cases)
                    default_' <- lowerDecisionTree selections' default_
                    let result = branchToDest dest (Low.BSwitch tag cases' default_')
                    pure $ blk' `thenBlock` result
        DSwitchStr access cases default_ -> do
            ((block, matchee), selections') <- first separateTerm <$> select access selections
            let matchee' = fromSized matchee -- We're accessing a string, which is a sized type
            let
                lowerCases = \case
                    [] -> lowerDecisionTree selections' default_
                    (s, dt) : cs -> do
                        s' <- internStr s
                        (block, isMatch) <- fmap separateTerm . emit =<< lowerStrEq
                            matchee'
                            (Low.OGlobal s')
                        conseq <- lowerDecisionTree selections' dt
                        alt <- lowerCases cs
                        pure $ block `thenBlock` branchToDest dest (Low.BIf isMatch conseq alt)
            block `thenBlockM` lowerCases (Map.toAscList cases)

    select
        :: Access
        -> Map Access (Sized Low.Operand)
        -> Lower (Low.Block (Sized Low.Operand), Map Access (Sized Low.Operand))
    select access selections = case Map.lookup access selections of
        Just x -> pure (Low.Block [] x, selections)
        Nothing -> do
            (val, selections') <- case access of
                TopSel{} ->
                    ice
                        $ "select: TopSel not in selections\nselector: "
                        ++ show access
                        ++ "\nselections: "
                        ++ show selections
                As a span' vi -> withSizedSelection a $ asVariant span' vi
                Sel a mi _span' -> withSizedSelection a $ \x ->
                    bindrBlockM' (lookupStruct (MemberId (fromIntegral mi)) x) $ \case
                        ZeroSized -> pure (Low.Block [] ZeroSized)
                        Sized m -> mapTerm Sized <$> deref m
                ADeref a -> withSizedSelection a $ fmap (mapTerm Sized) . deref
            pure (val, Map.insert access (Low.blockTerm val) selections')
      where
        withSizedSelection a f = do
            ((blk, x), selections') <- first separateTerm <$> select a selections
            y <- case x of
                ZeroSized -> pure $ Low.Block [] ZeroSized
                Sized x' -> f x'
            pure (blk `thenBlock` y, Map.insert access (Low.blockTerm y) selections')

        asVariant :: Span -> VariantIx -> Low.Operand -> Lower (Low.Block (Sized Low.Operand))
        asVariant 1 0 x = pure $ Low.Block [] (Sized x)
        asVariant 1 vi x =
            ice
                $ "Lower.asVariant: span is 1 but variant index is not 0, vi = "
                ++ show vi
                ++ ", x = "
                ++ show x
        asVariant _ vi x = do
            let tidData = case typeof x of
                    Low.TPtr (Low.TConst tid) -> tid
                    t ->
                        ice $ "Lower.asVariant: type of matchee is not TPtr to TConst, " ++ show t
            variantTypeId tidData vi >>= \case
                ZeroSized -> pure (Low.Block [] ZeroSized)
                Sized vtid -> do
                    let tvariant = Low.TPtr (Low.TConst vtid)
                    -- Skip tag to get inner union
                    (blk1, union) <- separateTerm <$> indexStruct 1 x
                    (blk2, v) <- separateTerm
                        <$> emit (Low.Expr (Low.EAsVariant union vi) tvariant)
                    pure (blk1 `thenBlock` blk2 `thenBlock` Low.Block [] (Sized v))

        deref :: Low.Operand -> Lower (Low.Block Low.Operand)
        deref ptr = keepOnStack (pointee (typeof ptr)) >>= \case
            True -> pure (Low.Block [] ptr)
            False -> load ptr

    selectVarBindings
        :: Map Access (Sized Low.Operand)
        -> [(TypedVar, Access)]
        -> Lower (Low.Block [(TypedVar, Low.Operand)])
    selectVarBindings selections = fmap fst . foldlM
        (\(block1, selections) (x, access) -> do
            (block2, ss') <- select access selections
            pure (block1 <> mapTerm (sized ((: []) . (x, )) []) block2, ss')
        )
        (Low.Block [] [], selections)

-- | Given the type ID of a tagged union or enum, and the pre-lowered index of a variant, returns
--   the type ID of the structure representing that variant, unless zero sized.
variantTypeId :: Low.TypeId -> VariantIx -> Lower (Sized Low.TypeId)
variantTypeId tidData variantIx = do
    lookupTypeId tidData >>= \case
        (_, Low.DStruct Low.Struct { Low.structMembers = [_tag, (_, union)] }) -> do
            let tidUnion = asTConst union
            variants <- lookupTypeId tidUnion <&> \case
                (_, Low.DUnion Low.Union { Low.unionVariants = vs }) -> vs
                x -> ice $ "Lower.variantTypeId: expected union, found " ++ show x
            pure $ snd (variants Vec.! fromIntegral variantIx)
        (_, Low.DEnum _) -> pure ZeroSized
        x -> ice $ "Lower.variantTypeId: expected tagged union or enum, found " ++ show x

lowerCtion
    :: Destination d
    => d
    -> VariantIx
    -> Span
    -> TConst
    -> [Expr]
    -> Lower (Low.Block (DestTerm d))
lowerCtion dest variantIx span tconst xs = queryTConst tconst >>= \case
    ZeroSized -> do
        blk <- catBlocks_ <$> mapM (lowerExpr Nowhere) xs
        blk `thenBlockM` sizedToDest dest ZeroSized
    Sized tidOuter -> do
        tdef <- lookupTypeId tidOuter
        let memberXs = zip (map MemberId [0 ..]) xs
        case snd tdef of
            Low.DUnion _ -> ice "lowerExpr Ction: outermost TypeDef was a union"
            Low.DEnum variants ->
                let operand = Low.OConst $ Low.EnumVal
                        { Low.enumType = tidOuter
                        , Low.enumVariant = variants Vec.! fromIntegral variantIx
                        , Low.enumWidth = tagBits span
                        , Low.enumVal = fromIntegral variantIx
                        }
                in  toDest dest $ Low.Expr (Low.EOperand operand) (typeof operand)
            Low.DStruct _ | span == 1 -> do
                (ptr, retVal) <- allocationAtDest dest Nothing (Low.TConst tidOuter)
                lowerExprsInStruct memberXs ptr <&> mapTerm (const retVal)
            Low.DStruct _ | otherwise -> do
                (ptr, retVal) <- allocationAtDest dest Nothing (Low.TConst tidOuter)
                Low.Block stms1 tagPtr <- indexStruct 0 ptr
                let stm2 = Low.Store (Low.OConst (lowerTag span variantIx)) tagPtr
                Low.Block stms3 () <- variantTypeId tidOuter variantIx >>= \case
                    ZeroSized -> catBlocks_ <$> mapM (lowerExpr Nowhere) xs
                    Sized tidVariant -> do
                        Low.Block stms'1 unionPtr <- indexStruct 1 ptr
                        Low.Block stms'2 variantPtr <- emit $ Low.Expr
                            (Low.EAsVariant unionPtr (fromIntegral tidVariant))
                            (Low.TPtr (Low.TConst tidVariant))
                        Low.Block stms'3 () <- lowerExprsInStruct memberXs variantPtr
                        pure $ Low.Block (stms'1 ++ stms'2 ++ stms'3) ()
                pure $ Low.Block (stms1 ++ stm2 : stms3) retVal

lowerTag :: Span -> VariantIx -> Low.Const
lowerTag span variantIx =
    Low.CNat { Low.natWidth = tagBits span, Low.natVal = fromIntegral variantIx }

-- Assumes that struct is kept on stack. Returns pointer to member, unless the member was zero sized.
lookupStruct :: MemberName -> Low.Operand -> Lower (Low.Block (Sized Low.Operand))
lookupStruct i x = do
    t <- fmap Low.TPtr . Low.lookupMember i <$> getTypeStruct (pointee (typeof x))
    case t of
        Nothing -> pure (Low.Block [] ZeroSized)
        Just t' -> mapTerm Sized <$> emit (Low.Expr (Low.EGetMember i x) t')

indexStruct :: MemberIx -> Low.Operand -> Lower (Low.Block Low.Operand)
indexStruct i x = do
    member <- (!! fromIntegral i) . Low.structMembers <$> getTypeStruct (pointee (typeof x))
    emit (Low.Expr (Low.EGetMember (fst member) x) (Low.TPtr (snd member)))

getTypeStruct :: Low.Type -> Lower Low.Struct
getTypeStruct = \case
    Low.TConst tid -> lookupTypeId tid <&> \case
        (_, Low.DStruct struct) -> struct
        tdef -> ice $ "Low.getTypeStruct: TypeDef in tenv is not DStruct: " ++ show tdef
    Low.TClosure{} -> getTypeStruct (builtinType "closure")
    t -> ice $ "Low.getTypeStruct: type is not a TConst: " ++ show t

withVars :: [(TypedVar, Low.Operand)] -> Lower a -> Lower a
withVars vs ma = foldl (flip (uncurry withVar)) ma vs

withVar :: TypedVar -> Low.Operand -> Lower a -> Lower a
withVar lhs rhs = locally localEnv (Map.insert lhs rhs)

builtinType :: String -> Low.Type
builtinType name =
    Low.TConst . fromIntegral . fromJust $ findIndex ((== name) . fst) builtinTypeDefs

builtinTypeDefs :: [Low.TypeDef]
builtinTypeDefs =
    -- closure: pointer to captures struct & function pointer, genericized
    [ ( "closure"
      , Low.DStruct Low.Struct
          { Low.structMembers = [(MemberId 0, Low.VoidPtr), (MemberId 1, Low.VoidPtr)]
          , Low.structAlignment = wordsize
          , Low.structSize = wordsize * 2
          }
      )
    ]

lowerParamTypes :: [Type] -> Lower [Low.Param ()]
lowerParamTypes pts = catMaybes <$> mapM (sizedToParam () <=< lowerType) pts

sizedToParam :: name -> Sized Low.Type -> Lower (Maybe (Low.Param name))
sizedToParam name = \case
    ZeroSized -> pure Nothing
    Sized t -> Just <$> toParam name t

toParam :: name -> Low.Type -> Lower (Low.Param name)
toParam name t = passByRef t <&> \case
    True -> Low.ByRef name t
    False -> Low.ByVal name t

paramLocal :: Low.Param Low.LocalId -> Low.Local
paramLocal = \case
    Low.ByVal name t -> Low.Local name t
    Low.ByRef name t -> Low.Local name (Low.TPtr t)

toRet :: Lower name -> Sized Low.Type -> Lower (Maybe (Low.OutParam name), Low.Ret)
toRet genName = \case
    ZeroSized -> pure (Nothing, Low.RetVoid)
    Sized t -> passByRef t >>= \case
        True -> genName <&> \name -> (Just (OutParam name t), Low.RetVoid)
        False -> pure (Nothing, Low.RetVal t)

-- TODO: Should respect platform ABI. For example wrt size of TNatSize on 32-bit vs. 64-bit
--       platform.
--
-- | The Low representation of a type in expression-context
lowerType :: Type -> Lower (Sized Low.Type)
lowerType = \case
    TPrim (TNat w) -> pure $ mapSized Low.TNat (intWidthCeil w)
    TPrim TNatSize -> pure $ mapSized Low.TNat (intWidthCeil wordsizeBits)
    TPrim (TInt w) -> pure $ mapSized Low.TInt (intWidthCeil w)
    TPrim TIntSize -> pure $ mapSized Low.TInt (intWidthCeil wordsizeBits)
    TPrim TF32 -> pure $ Sized Low.TF32
    TPrim TF64 -> pure $ Sized Low.TF64
    TFun tparams tret -> do
        -- Not destructuring the tuple immediately is more lazy, and we need to be lazy since we're
        -- tying the knot in definedData.
        ret <- toRet (pure ()) =<< lowerType tret
        params <- lowerParamTypes tparams
        let captures = Low.ByVal () Low.VoidPtr
        pure (Sized (Low.TClosure (fst ret) (captures : params) (snd ret)))
    TBox t -> lowerType t <&> \case
        ZeroSized -> Sized Low.VoidPtr
        Sized t' -> Sized $ Low.TPtr t'
    TConst tc -> mapSized Low.TConst <$> queryTConst tc
  where
    intWidthCeil :: Word32 -> Sized Word
    intWidthCeil w = if
        | w == 0 -> ZeroSized
        | w <= 8 -> Sized 8
        | w <= 16 -> Sized 16
        | w <= 32 -> Sized 32
        | w <= 64 -> Sized 64
        | otherwise -> ice "Lower.lowerType: integral type larger than 64-bit"

-- TODO: Maybe compute sizes of all datatypes before lowering, working on Inferred, Checked, or
--       Monomorphic AST. Since we already have a Sizeof for that, it wouldn't be too much work,
--       and we wouldn't need to worry about infinite recursion when tying the knot hereabouts.
--
-- | Query the type environment for the Low TypeId of an AST TConst, lowering the associated type
--   definition on-demand and memoizing the result for future queries.
--
--   Assumes that the TConst actually has a corresponding definition in the collection of datatype
--   definitions given from the previous pass.
queryTConst :: Ast.TConst -> Lower (Sized Low.TypeId)
queryTConst x = do
    use (tenv . tids . to (Map.lookup x)) >>= \case
        Just tid -> pure tid
        Nothing -> defineDataOf x

  where
    defineDataOf x = defineData x =<< use (tenv . datas . to (Map.! x))

    -- | How the different sorts of types are represented in Carth:
    --
    --   Zero sized types are treated like void in C -- you can't have a value of type void, but
    --   void can be used as something like a type in certain contexts, like function returns.
    --
    --   An Enum is represented as the smallest integer type that can fit all variants.
    --
    --   A Data is equivalent to a tagged union, and is represented by a struct that consists of 2
    --   members: an integer that can fit the variant index followed by the second member which is
    --   a union type of structures representing each sized variant.
    defineData :: Ast.TConst -> [(String, VariantTypes)] -> Lower (Sized Low.TypeId)
    defineData tconst@(name, _) variants = dataIsSized variants >>= \case
        False -> pure ZeroSized
        True -> do
            tid <- fromIntegral . Seq.length <$> use (tenv . tdefs)
            modifying (tenv . tids) (Map.insert tconst (Sized tid))
            tdef <- mfix $ \tdef -> do
                modifying (tenv . tdefs) (Seq.|> tdef)
                lowerData name variants
            -- Can't do this in the `mfix` while we're tying the knot. I guess since we lookup in
            -- tdefIds every time defineTypeDef is called, and its order cannot be decided until
            -- tdef is fully computed. So we might get a few more duplicates this way, but
            -- whatever, it's fine.
            modifying (tenv . tdefIds) (Map.insert tdef tid)
            pure (Sized tid)

    dataIsSized :: [(String, VariantTypes)] -> Lower Bool
    dataIsSized = \case
        [] -> pure False
        [(_, ts)] -> or <$> mapM isSized ts
        _ : _ : _ -> pure True

    isSized :: Ast.Type -> Lower Bool
    isSized = \case
        TPrim _ -> pure True
        TFun _ _ -> pure True
        TBox _ -> pure True
        TConst x -> dataIsSized =<< use (tenv . datas . to (Map.! x))

    lowerData :: String -> [(String, VariantTypes)] -> Lower Low.TypeDef
    lowerData name variants = do
        -- let xs = map fst variants
        -- tss <- mapM (mapM lowerType . snd) variants
        variants' <- mapM
            (secondM $ fmap catMaybes . zipWithM
                (\i t -> fmap (MemberId i, ) . sizedMaybe <$> lowerType t)
                [0 ..]
            )
            variants
        case variants' of
            [] -> unreachable
            _ | all (null . snd) variants' ->
                pure (name, Low.DEnum (Vec.fromList (map fst variants')))
            [(_, members)] -> (name, ) <$> structDef members
            _ -> do
                -- tidInner <- defineUnion (name ++ "_union") variants' sMax aMax
                tidInner <- defineUnion (name ++ "_union") variants'
                let tag = Low.TNat (tagBits (fromIntegral (length variants')))
                -- outerStruct <- structDef [tag, Low.TConst tidInner]
                outerStruct <- structDef [(MemberId 0, tag), (MemberId 1, Low.TConst tidInner)]
                pure (name, outerStruct)

-- | Assumes that there are at least two variants, and that at least one variant has at least one
--   member.
defineUnion :: String -> [(String, [(MemberName, Low.Type)])] -> Lower Low.TypeId
defineUnion name variants = do
    variants' <- mapM
        (\case
            (vname, []) -> pure (vname, ZeroSized)
            (vname, ms) -> (vname, ) . Sized <$> defineStruct vname ms
        )
        variants
    let ts = map Low.TConst (catSized (map snd variants'))
    sMax <- maximum <$> mapM sizeof ts
    aMax <- maximum <$> mapM alignmentof ts
    defineTypeDef
        ( name
        , Low.DUnion Union { unionVariants = Vec.fromList variants'
                           , unionGreatestSize = sMax
                           , unionGreatestAlignment = aMax
                           }
        )

-- | Assumes that member list is nonempty
defineStruct :: String -> [(MemberName, Low.Type)] -> Lower Low.TypeId
defineStruct name members = defineTypeDef . (name, ) =<< structDef members

defineTypeDef :: Low.TypeDef -> Lower Low.TypeId
defineTypeDef tdef = do
    use (tenv . tdefIds . to (Map.lookup tdef)) >>= \case
        Just tid -> pure tid
        Nothing -> do
            tid <- fromIntegral . Seq.length <$> use (tenv . tdefs)
            modifying (tenv . tdefs) (Seq.|> tdef)
            modifying (tenv . tdefIds) (Map.insert tdef tid)
            pure tid

-- | Assumes that member list is nonempty
structDef :: [(MemberName, Low.Type)] -> Lower Low.TypeDef'
structDef ms =
    let ts = map snd ms
    in  liftM2 (Low.DStruct .* Low.Struct ms) (alignmentofStruct ts) (sizeofStruct ts)

sizedMembers :: [Sized Low.Type] -> [(MemberName, Low.Type)]
sizedMembers = catMaybes . zipWith (\i t -> fmap (MemberId i, ) (sizedMaybe t)) [0 ..]

-- | Assumes that the given TypeId is live and valid, i.e. that it was first given to you by
--   `lowerType` or something.
lookupTypeId :: Low.TypeId -> Lower Low.TypeDef
lookupTypeId tid = use (tenv . tdefs . to (`Seq.index` fromIntegral tid))

asTFun :: Low.Type -> (Maybe (Low.OutParam ()), [Low.Param ()], Low.Ret)
asTFun = \case
    Low.TFun outParam params ret -> (outParam, params, ret)
    t -> ice $ "Lower.asTFun of non function type " ++ show t

asTClosure :: Low.Type -> (Maybe (Low.OutParam ()), [Low.Param ()], Low.Ret)
asTClosure = \case
    Low.TClosure outParam params ret -> (outParam, params, ret)
    t -> ice $ "Lower.asTClosure of non closure type " ++ show t

returnee :: Low.Type -> Low.Ret
returnee t = let (_, _, r) = asTFun t in r

lowerArgs :: [Expr] -> Lower (Low.Block [Low.Operand])
lowerArgs as = mapTerm catSized <$> lowerEmitExprs Arg emitSized as

lowerEmitExprs
    :: Destination d
    => d
    -> (DestTerm d -> Lower (Low.Block op))
    -> [Expr]
    -> Lower (Low.Block [op])
lowerEmitExprs dest emit as = catBlocks <$> mapM (bindBlockM emit <=< lowerExpr dest) as

catBlocks :: [Low.Block a] -> Low.Block [a]
catBlocks = mconcat . map (mapTerm pure)

catBlocks_ :: [Low.Block ()] -> Low.Block ()
catBlocks_ = mconcat . map (mapTerm (const ()))

-- NOTE: This post is helpful:
--       https://stackoverflow.com/questions/42411819/c-on-x86-64-when-are-structs-classes-passed-and-returned-in-registers
--       Also, official docs: https://refspecs.linuxbase.org/elf/x86_64-abi-0.99.pdf particularly
--       section 3.2.3 Parameter Passing (p18).
--
--       From SystemV x86-64 ABI: "The size of each argument gets rounded up to eightbytes."  "the
--       term eightbyte refers to a 64-bit object" "If the size of an object is larger than four
--       eightbytes, or it contains unaligned fields, it has class MEMORY" "If the size of the
--       aggregate exceeds two eightbytes and the first eight-byte isn’t SSE or any other eightbyte
--       isn’t SSEUP, the whole argument is passed in memory.""
--
--       Essentially, for Carth, I think it's true that all aggregate types of size > 2*8 bytes are
--       passed in memory, and everything else is passed in register. We could always state that
--       this is the ABI we use, and that it's the user's responsibility to manually handle the
--       cases where it may clash with the correct C ABI. Maybe we'll want to revisit this if/when
--       we add support for SIMD vector types something similarly exotic.
passByRef :: Low.Type -> Lower Bool
passByRef t = sizeof t <&> (> 2 * 8)

sizeof :: Low.Type -> Lower Word
sizeof = tdefsHelper Low.sizeof

alignmentof :: Low.Type -> Lower Word
alignmentof = tdefsHelper Low.alignmentof

sizeofStruct :: [Low.Type] -> Lower Word
sizeofStruct = tdefsHelper Low.sizeofStruct

alignmentofStruct :: [Low.Type] -> Lower Word
alignmentofStruct = tdefsHelper Low.alignmentofStruct

tdefsHelper :: ((Low.TypeId -> Low.TypeDef) -> a -> b) -> a -> Lower b
tdefsHelper f x = use (tenv . tdefs) <&> \tdefs' -> f (Seq.index tdefs' . fromIntegral) x

keepOnStack :: Low.Type -> Lower Bool
keepOnStack = \case
    Low.TClosure{} -> pure True
    Low.TConst tid -> lookupTypeId tid <&> \case
        (_, Low.DStruct _) -> True
        (_, Low.DUnion _) -> True
        (_, Low.DEnum _) -> False
    _ -> pure False

funDefGlobal :: Low.FunDef -> Low.Global
funDefGlobal Low.FunDef { Low.funDefName = x, Low.funDefOutParam = out, Low.funDefParams = ps, Low.funDefRet = r }
    = Low.Global
        x
        (Low.TFun (fmap (\o -> o { outParamName = () }) out) (map Low.dropParamName ps) r)

stackAlloc :: Maybe String -> Low.Type -> Lower Low.Operand
stackAlloc name t = do
    x <- newLName (fromMaybe "tmp" name)
    modifying allocs ((x, t) :)
    pure (Low.OLocal (Low.Local x (Low.TPtr t)))

newLName :: String -> Lower Low.LocalId
newLName x = do
    localId <- Seq.length <$> use localNames
    modifying localNames (Seq.|> x)
    pure (fromIntegral localId)

newGName :: String -> Lower Low.GlobalId
newGName x = do
    globalId <- Seq.length <$> use globalNames
    modifying globalNames (Seq.|> x)
    pure (fromIntegral globalId)

mapTerm :: (a -> b) -> Low.Block a -> Low.Block b
mapTerm f b = b { Low.blockTerm = f (Low.blockTerm b) }

separateTerm :: Low.Block a -> (Low.Block (), a)
separateTerm (Low.Block stms term) = (Low.Block stms (), term)

mapBranchTerm :: (a -> b) -> Low.Branch a -> Low.Branch b
mapBranchTerm f = \case
    Low.BIf p c a -> Low.BIf p (mapTerm f c) (mapTerm f a)
    Low.BSwitch m cs d -> Low.BSwitch m (map (second (mapTerm f)) cs) (mapTerm f d)

branchGetSomeTerm :: Low.Branch a -> a
branchGetSomeTerm (Low.BIf _ c _) = Low.blockTerm c
branchGetSomeTerm (Low.BSwitch _ _ d) = Low.blockTerm d

thenBlock :: Low.Block () -> Low.Block a -> Low.Block a
thenBlock (Low.Block stms1 ()) (Low.Block stms2 a) = Low.Block (stms1 ++ stms2) a

thenBlockM :: Low.Block () -> Lower (Low.Block a) -> Lower (Low.Block a)
thenBlockM b1 mb2 = bindrBlockM b1 (\() -> mb2)

bindBlockM :: Monad m => (a -> m (Low.Block b)) -> Low.Block a -> m (Low.Block b)
bindBlockM f (Low.Block stms1 a) = f a <&> \(Low.Block stms2 b) -> Low.Block (stms1 ++ stms2) b

bindrBlockM :: Monad m => Low.Block a -> (a -> m (Low.Block b)) -> m (Low.Block b)
bindrBlockM = flip bindBlockM

bindBlockM' :: Monad m => (a -> m (Low.Block b)) -> m (Low.Block a) -> m (Low.Block b)
bindBlockM' f ma = bindBlockM f =<< ma

bindrBlockM' :: Monad m => m (Low.Block a) -> (a -> m (Low.Block b)) -> m (Low.Block b)
bindrBlockM' = flip bindBlockM'

addIndirection :: Low.Operand -> Lower (Low.Block Low.Operand)
addIndirection v = do
    onStack <- keepOnStack (typeof v)
    if onStack
        then do
            ptr <- stackAlloc Nothing (typeof v)
            pure $ Low.Block [Low.Store v ptr] ptr
        else pure $ Low.Block [] v

addIndirectionE :: Low.Expr -> Lower (Low.Block Low.Expr)
addIndirectionE e = do
    onStack <- keepOnStack (typeof e)
    if onStack
        then do
            Low.Block stms1 v <- emit e
            ptr <- stackAlloc Nothing (typeof v)
            let stm2 = Low.Store v ptr
            pure $ Low.Block (stms1 ++ [stm2]) (Low.Expr (Low.EOperand ptr) (typeof ptr))
        else pure $ Low.Block [] e

emit :: Low.Expr -> Lower (Low.Block Low.Operand)
emit = emitNamed "tmp"

emitNamed :: String -> Low.Expr -> Lower (Low.Block Low.Operand)
emitNamed _ (Low.Expr (Low.EOperand x) _) = pure (Low.Block [] x)
emitNamed name e = do
    name' <- newLName name
    let l = Low.Local name' (typeof e)
    pure (Low.Block [Low.Let l e] (Low.OLocal l))

emitSized :: Sized Low.Expr -> Lower (Low.Block (Sized Low.Operand))
emitSized = \case
    ZeroSized -> pure $ Low.Block [] ZeroSized
    Sized e -> mapTerm Sized <$> emit e

load :: Low.Operand -> Lower (Low.Block Low.Operand)
load addr = emit $ Low.Expr (Low.Load addr) (pointee (typeof addr))

loadE :: Low.Expr -> Lower (Low.Block Low.Expr)
loadE addr = emit addr <&> mapTerm (\addr' -> Low.Expr (Low.Load addr') (pointee (typeof addr')))

replaceLocalNames :: Seq String -> Lower (Seq String)
replaceLocalNames ns = localNames <<.= ns

replaceAllocs :: [(Low.LocalId, Low.Type)] -> Lower [(Low.LocalId, Low.Type)]
replaceAllocs as = reverse <$> (allocs <<.= as)
