{-# LANGUAGE TemplateHaskell, DataKinds, InstanceSigs, ScopedTypeVariables, RankNTypes #-}

module Back.Lower (lower) where

import qualified Codec.Binary.UTF8.String as UTF8.String
import Control.Arrow
import Control.Monad
import Control.Monad.RWS
import Data.Bifunctor (bimap)
import Data.Bitraversable
import Data.Either
import Data.Foldable
import Data.Functor
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Vector as Vec
import Data.Word
import Lens.Micro.Platform (makeLenses, modifying, use, view, (<<.=), (.=), to)

import Back.Low (typeof)
import qualified Back.Low as Low
import Front.Monomorphize as Ast
import Front.Monomorphic as Ast
import Front.TypeAst as Ast hiding (TConst)
import Misc
import Sizeof
import FreeVars

data Sized x = ZeroSized | Sized x

mapSized :: (a -> b) -> Sized a -> Sized b
mapSized f (Sized a) = Sized (f a)
mapSized _ ZeroSized = ZeroSized

mapSizedM :: Monad m => (a -> m b) -> Sized a -> m (Sized b)
mapSizedM f = \case
    Sized a -> fmap Sized (f a)
    ZeroSized -> pure ZeroSized

data St = St
    { _strLits :: Map String Low.GlobalId
    , _allocs :: [(Low.LocalId, Low.Type)]
    , _localNames :: Seq String
    , _globalNames :: Seq String
    -- Iff a TConst is zero sized, it will have no entry
    , _tconsts :: Map TConst Low.TypeId
    , _tids :: Seq Low.TypeDef -- ^ Maps type IDs as indices to type defs
    , _tdefs :: Map Low.TypeDef Low.TypeId
    }
makeLenses ''St

-- We need to be able to generate (pseudo) anonymous structs as part of lowering.
-- For example, a named struct needs to be defined for each captures struct of a closure.
-- In LLVM backend, this is not strictly necessary, as we can use anonymous structs. Naming
-- them implies shorter lines and less noise though, so that's still a good idea.
-- In C, anonymous structs are uniqued, and can't be "reused", so we will need to name them for
-- things to even work.

-- Just added (& renamed / modified) tids and tenv to St. This will affect a bunch of code, since
-- existing in the big `where` is no longer enough to access all of the type environment.
-- Things like `sizeof` needs to be in a `Lower` monad now, so yeah. Fixing that and implementing
-- lowerExpr for Fun is what's currently going on.

-- data TailPos = TailRet | TailOutParam Low.LocalId | NoTail

data Env = Env
    { _localEnv :: Map TypedVar Low.Operand
    , _globalEnv :: Map TypedVar Low.Global
    -- | Each extern function comes coupled with a wrapper function that accepts &
    --   discards a closure captures parameter.
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

-- | A potentially not yet emitted&named operand
-- type PartialOperand = Either Low.Expr Low.Operand
-- type EBlock = Low.Block (Sized PartialOperand)

-- Regarding the stack and registers.
--
-- I'm thinking we could generate Low IR such that all structs & unions are on the stack,
-- which means they would require an Alloc and the type would be behind a TPtr. All
-- primitive types would be in registers. This would simplify Lower. We would for example
-- not need both an ExtractElement and GetElementPointer, like in LLVM. Only a GEP would
-- do, since we keep all structs on the stack.
--
-- We assume then that the next codegen step in the pipe will do register allocation, and
-- optimize such that small structs are kept in register instead of on the stack etc.

class Destination d where
    type DestTerm d
    toDest :: d -> Sized Low.Expr -> Lower (Low.Block (DestTerm d))
    branchToDest :: d -> Low.Branch (DestTerm d) -> Low.Block (DestTerm d)
    allocationAtDest :: d -> Maybe String -> Low.Type -> Lower (Low.Operand, DestTerm d)

newtype There = There Low.Operand deriving Show
instance Destination There where
    type DestTerm There = ()

    toDest (There a) = \case
        ZeroSized -> ice "Lower.toDest: ZeroSized to There"
        Sized e -> do
            Low.Block stms1 x <- emit e
            Low.Block stms2 x' <- if typeof x == typeof a
                then load x
                else pure (Low.Block [] x)
            pure $ Low.Block (stms1 ++ stms2 ++ [Low.Store x' a]) ()

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

    toDest (ThereSized a) = \case
        ZeroSized -> pure (Low.Block [] ZeroSized)
        e -> mapTerm Sized <$> toDest (There a) e

    branchToDest (ThereSized _) br =
        Low.Block [Low.SBranch (mapBranchTerm (const ()) br)] (branchGetSomeTerm br)

    allocationAtDest (ThereSized addr) name t =
        second Sized <$> allocationAtDest (There addr) name t

data Here = Here
    deriving Show
instance Destination Here where
    type DestTerm Here = Low.Expr

    toDest Here = \case
        ZeroSized -> ice "Lower.toDest: ZeroSized to Here"
        Sized e -> pure $ Low.Block [] e

    branchToDest Here br =
        Low.Block [] (Low.Expr (Low.EBranch br) (typeof (branchGetSomeTerm br)))

    allocationAtDest Here =
        fmap (\x -> (x, Low.Expr (Low.EOperand x) (typeof x))) .* stackAlloc

data HereSized = HereSized
    deriving Show
instance Destination HereSized where
    type DestTerm HereSized = Sized Low.Expr

    toDest HereSized = pure . Low.Block []

    branchToDest HereSized br = case branchGetSomeTerm br of
        Sized _ -> mapTerm Sized $ branchToDest Here (mapBranchTerm fromSized br)
        ZeroSized -> Low.Block [Low.SBranch (mapBranchTerm (const ()) br)] ZeroSized

    allocationAtDest HereSized =
        fmap (\x -> (x, Sized $ Low.Expr (Low.EOperand x) (typeof x))) .* stackAlloc

data Nowhere = Nowhere
    deriving Show
instance Destination Nowhere where
    type DestTerm Nowhere = ()

    toDest Nowhere = \case
        ZeroSized -> pure $ Low.Block [] ()
        Sized _ -> ice "Lower.toDest: Sized to Nowhere"

    branchToDest Nowhere br = Low.Block [Low.SBranch br] ()

    allocationAtDest Nowhere _ _ = ice "Lower.allocationAtDest: allocation at Nowhere"

lower :: Bool -> Program -> Low.Program
lower noGC (Program (Topo defs) datas externs) =
    let
        externNames = map fst externs
        (gfunDefs, gvarDefs) = partitionGlobDefs
        (funLhss, funRhss) = unzip gfunDefs
        (varLhss, varRhss) = unzip gvarDefs
        (((externs', externWrappers), varDecls', mainId), st, out) = runLower $ do
            defineDatas
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
                      mainId' <- view
                          (globalEnv . to (Map.! TypedVar "main" Ast.mainType))
                      pure
                          ( unzip (map snd externs'')
                          , mapMaybe (fmap (uncurry Low.GlobVarDecl) . sizedMaybe)
                                     varDecls
                          , mainId'
                          )
        names = Vec.fromList $ resolveNameConflicts ("main" : externNames)
                                                    (toList (view globalNames st))
        fs = view outFunDefs out
        cs = map (\(gid, t, c) -> Low.GlobConstDef gid t c) (view outConstDefs out)
        tenv = toList (view tids st)
        tnames = resolveNameConflicts [] (map fst tenv)
        tenv' = Vec.fromList $ zip tnames (map snd tenv)
    in
        Low.Program (externWrappers ++ fs) externs' (cs ++ varDecls') tenv' names mainId
  where
    runLower la = runRWS la initEnv initSt
    initSt = St { _strLits = Map.empty
                , _allocs = []
                , _localNames = Seq.empty
                , _globalNames = builtinNames
                , _tconsts = Map.empty
                , _tids = Seq.empty
                , _tdefs = Map.empty
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
            in  if Map.member name' seen
                    then incrementUntilUnseen seen (n + 1) name
                    else (n, name')

    -- In addition to lowering the extern declaration directly, also generates a wrapping
    -- function that accepts & discards a closure captures parameter.
    lowerExterns :: Lower [(TypedVar, (Low.ExternDecl, Low.FunDef))]
    lowerExterns = forM externs $ \case
        (name, t@(TFun pts rt)) -> do
            (outParam, ret) <- toRet (pure ()) =<< lowerType rt
            ps <- lowerParamTypes pts
            let decl = Low.ExternDecl name (maybe id (:) outParam ps) ret
                operand = Low.OExtern (externDeclToExtern decl)
            wrapperName <- newGName (name ++ "_wrapper")
            let capturesParam = Low.ByVal () Low.VoidPtr
                wrapperParams = zipWith Low.addParamName
                                        [0 ..]
                                        (maybe id (:) outParam $ capturesParam : ps)
                wrapperParamLocals = map (Low.OLocal . paramLocal) wrapperParams
                callExternWithoutCaptures = case (outParam, ret) of
                    (Nothing, Low.RetVoid) -> Low.Block
                        [Low.VoidCall operand (deleteAt 0 wrapperParamLocals)]
                        Low.TRetVoid
                    (Just _, Low.RetVoid) -> Low.Block
                        [Low.VoidCall operand (deleteAt 1 wrapperParamLocals)]
                        Low.TRetVoid
                    (_, Low.RetVal t) -> Low.Block [] . Low.TRetVal $ Low.Expr
                        (Low.Call operand (deleteAt 0 wrapperParamLocals))
                        t
                wrapper = Low.FunDef
                    wrapperName
                    wrapperParams
                    ret
                    callExternWithoutCaptures
                    []
                    (Vec.fromList
                    . take (length wrapperParams)
                    $ (if isJust outParam then ("sret" :) else id)
                    $ "_captures"
                    : map (\i -> "x" ++ show i) [0 :: Word ..]
                    )
            pure (TypedVar name t, (decl, wrapper))
        (name, t) -> nyi $ "lower: Non-function externs: " ++ name ++ ", " ++ show t

    declareGlobVar :: TypedVar -> Low.GlobalId -> Lower (Sized (Low.GlobalId, Low.Type))
    declareGlobVar tv gid = mapSized (gid, ) <$> lowerType (tvType tv)

    withExterns :: [(TypedVar, (Low.ExternDecl, Low.FunDef))] -> Lower a -> Lower a
    withExterns es = locallySet
        externEnv
        (Map.fromList (map (second (bimap externDeclToExtern funDefGlobal)) es))

    externDeclToExtern (Low.ExternDecl x ps r) = Low.Extern x ps r

    withGlobFuns :: [(TypedVar, Low.GlobalId)] -> Lower a -> Lower a
    withGlobFuns fs ma = do
        fs' <- forM fs $ \(tv, gid) ->
            (tv, )
                . Low.Global gid
                . uncurry Low.TFun
                . asTClosure
                . fromSized
                <$> lowerType (tvType tv)
        augment globalEnv (Map.fromList fs') ma

    withGlobVars :: [(TypedVar, Sized (Low.GlobalId, Low.Type))] -> Lower a -> Lower a
    withGlobVars vs = augment globalEnv . Map.fromList $ mapMaybe
        (\(tv, g) -> fmap ((tv, ) . uncurry Low.Global . second Low.TPtr) (sizedMaybe g))
        vs

    defineInit :: [(Sized (Low.GlobalId, Low.Type), Expr)] -> Lower Low.FunDef
    defineInit varDefs = do
        block <- mapTerm (const Low.TRetVoid) . catBlocks <$> mapM defineGlobVar varDefs
        localNames' <-
            Vec.fromList
            . resolveNameConflicts []
            . toList
            <$> replaceLocalNames Seq.empty
        allocs' <- replaceAllocs []
        pure $ Low.FunDef initName [] Low.RetVoid block allocs' localNames'

    defineGlobVar :: (Sized (Low.GlobalId, Low.Type), Expr) -> Lower (Low.Block ())
    defineGlobVar (g, e) = case g of
        Sized (gid, t) -> do
            let ref = Low.Global gid (Low.TPtr t)
            -- Fix for Boehm GC to detect global vars when running in JIT
            blk <- gcAddRoot ref
            blk `thenBlockM` lowerExpr (There (Low.OGlobal ref)) e
        ZeroSized -> lowerExpr Nowhere e
      where
        -- | Must be used on globals when running in JIT, as Boehm GC only detects global var
        --   roots when it can scan some segment in the ELF.
        gcAddRoot :: Low.Global -> Lower (Low.Block ())
        gcAddRoot globRef = if noGC
            then pure (Low.Block [] ())
            else do
                let p0 = Low.CBitcast (Low.CGlobal globRef) (Low.TPtr (Low.TNat 8))
                    ptrSize = 8
                    p1 = Low.CPtrIndex p0 ptrSize
                stm <- fromRight (ice "GC_add_roots, not a void call")
                    <$> callBuiltin "GC_add_roots" [Low.OConst p0, Low.OConst p1]
                pure (Low.Block [stm] ())

    lowerFunDef
        :: [TypedVar] -> Maybe TypedVar -> Low.GlobalId -> Fun -> Lower Low.FunDef
    lowerFunDef freeLocals lhs name (ps, (body, rt)) = locallySet localEnv Map.empty $ do
        -- Gotta remember these for when we return to whichever scope we came from
        oldLocalNames <- replaceLocalNames Seq.empty
        oldAllocs <- replaceAllocs []
        -- Zero-sized parameters don't actually get to exist in the Low IR and beyond
        (binds, innerParamIds, directParamTs) <-
            fmap (unzip3 . catMaybes) $ forM ps $ \p -> lowerType (tvType p) >>= \case
                ZeroSized -> pure Nothing
                Sized pt -> do
                    pid <- newLName (tvName p)
                    let bind = (p, Low.OLocal (Low.Local pid pt))
                    pure (Just (bind, pid, pt))
        capturesName <- newLName "captures"
        rt' <- lowerType rt
        (outParam, ret) <- toRet (newLName "sret") rt'
        paramTs <- mapM
            (\t -> passByRef t <&> \case
                True -> Low.TPtr t
                False -> t
            )
            directParamTs
        let innerParams = zipWith Low.Local innerParamIds paramTs
        Low.Block capturesStms capturesBinds <- unpackCaptures capturesName freeLocals
        anonParams <-
            maybe id ((:) . Low.dropParamName) outParam
            . (Low.ByVal () Low.VoidPtr :)
            <$> mapM (sizedToParam ()) directParamTs
        let tselfFun = Low.TFun anonParams ret
            selfCaptures = Low.OLocal $ Low.Local capturesName Low.VoidPtr
            selfRef = Low.Global name tselfFun
            selfFun' = fmap (, selfCaptures, selfRef) lhs
        -- Lower the body, generate an out-parameter if the return value is to be passed
        -- on the stack, and optimize to loop if the function is tail recursive.
        (outerParamIds, body'') <- locallySet selfFun selfFun' $ do
            -- These will be discarded if the function is not tail recursive. In that
            -- case, the inner params and the outer params are the same.
            outerParamIds <- mapM spinoffLocalId innerParamIds
            let outerParams = zipWith Low.Local outerParamIds paramTs
            withVars (capturesBinds ++ binds) $ case (outParam, ret) of
                (Nothing, Low.RetVoid) -> do
                    body' <- lowerExpr Nowhere body
                    pure $ if isTailRec_RetVoid name body'
                        then
                            ( outerParamIds
                            , tailCallOpt_RetVoid name outerParams innerParams body'
                            )
                        else (innerParamIds, mapTerm (\() -> Low.TRetVoid) body')
                (Nothing, Low.RetVal rt) -> do
                    body' <- bindBlockM (removeIndirectionE rt) =<< lowerExpr Here body
                    pure $ if isTailRec_RetVal name body'
                        then
                            ( outerParamIds
                            , tailCallOpt_RetVal name outerParams innerParams body'
                            )
                        else (innerParamIds, mapTerm Low.TRetVal body')
                (Just outParam', Low.RetVoid) -> do
                    let outParamOp = Low.OLocal $ paramLocal outParam'
                    body' <- lowerExpr (There outParamOp) body
                    pure $ if isTailRec_RetVoid name body'
                        then
                            ( outerParamIds
                            , tailCallOpt_RetVoid name outerParams innerParams body'
                            )
                        else (innerParamIds, mapTerm (\() -> Low.TRetVoid) body')
                (Just _, Low.RetVal _) -> unreachable
        let body''' = Low.Block capturesStms () `thenBlock` body''
        localNames' <-
            Vec.fromList
            . resolveNameConflicts []
            . toList
            <$> replaceLocalNames oldLocalNames
        allocs' <- replaceAllocs oldAllocs
        outerParams <- zipWithM sizedToParam outerParamIds directParamTs
        let params =
                maybe id (:) outParam $ Low.ByVal capturesName Low.VoidPtr : outerParams
        pure $ Low.FunDef name params ret body''' allocs' localNames'

    replaceLocalNames ns = localNames <<.= ns
    replaceAllocs as = reverse <$> (allocs <<.= as)

    unpackCaptures
        :: Low.LocalId -> [TypedVar] -> Lower (Low.Block [(TypedVar, Low.Operand)])
    unpackCaptures capturesName freeVars = typedVarsSizedTypes freeVars >>= \case
        [] -> pure (Low.Block [] [])
        vars -> do
            let capturesGeneric = Low.OLocal $ Low.Local capturesName Low.VoidPtr
            tcaptures <- defineStruct "captures" $ map (first tvName) vars
            captures <-
                let t = Low.TPtr tcaptures
                in  emitNamed "captures" (Low.Expr (Low.Bitcast capturesGeneric t) t)
            captures `bindrBlockM` \captures' -> catBlocks <$> mapM
                (\(i, (v@(TypedVar x _), t)) -> mapTerm (v, )
                    <$> emitNamed x (Low.Expr (Low.EGetMember i captures') (Low.TPtr t))
                )
                (zip [0 ..] vars)

    isTailRec_RetVoid self = go
      where
        go (Low.Block stms ()) = case lastMay stms of
            Just (Low.VoidCall (Low.OGlobal (Low.Global other _)) _) | other == self ->
                True
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
            Low.VoidCall (Low.OGlobal (Low.Global other _)) args | other == self ->
                Low.Block [] (Low.Continue (drop (length args - length outerParams) args))
            Low.SBranch br -> goBranch br
            stm -> Low.Block [stm] (Low.Break ())
        goBranch = \case
            Low.BIf pred conseq alt ->
                Low.Block [] . Low.LBranch $ Low.BIf pred (go conseq) (go alt)
            Low.BSwitch matchee cases default' ->
                Low.Block [] . Low.LBranch $ Low.BSwitch matchee
                                                         (map (second go) cases)
                                                         (go default')
        go (Low.Block stms ()) =
            let (initStms, lastStm) = fromJust (unsnoc stms)
                termBlock = goStm lastStm
            in  Low.Block initStms () `thenBlock` termBlock

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
            Low.BSwitch matchee cases default' ->
                Low.Block [] . Low.LBranch $ Low.BSwitch matchee
                                                         (map (second go) cases)
                                                         (go default')

    spinoffLocalId :: Low.LocalId -> Lower Low.LocalId
    spinoffLocalId x = do
        names <- use localNames
        let name = Seq.index names (fromIntegral x)
        newLName name

    lowerExpr :: (Show d, Destination d) => d -> Expr -> Lower (Low.Block (DestTerm d))
    lowerExpr dest = \case
        Lit c -> toDest dest . Sized . operandToExpr =<< lowerConst c
        Var _ x -> lookupVar dest x
        App f as -> lowerApp dest f as
        If pred conseq alt ->
            lowerExpr Here pred
                `bindrBlockM'` emitNamed "predicate"
                `bindrBlockM'` \pred' -> do
                                   conseq' <- lowerExpr dest conseq
                                   alt' <- lowerExpr dest alt
                                   pure . branchToDest dest $ Low.BIf pred' conseq' alt'
        Fun f -> lowerLambda dest f
        Let (VarDef (lhs, (_, rhs))) body -> lowerExpr HereSized rhs `bindrBlockM'` \case
            ZeroSized -> lowerExpr dest body
            Sized rhs' -> bindrBlockM' (emit rhs')
                $ \rhs'' -> withVar lhs rhs'' (lowerExpr dest body)
        Let (RecDefs defs) body -> do
            let lhss = Set.fromList $ map fst defs
            Low.Block stms1 (binds, cs) <-
                fmap (mapTerm unzip . catBlocks) . forM defs $ \(lhs, (_, f)) -> do
                    (freeLocalVars, captures) <- precaptureFreeLocalVars
                        (Set.delete lhs lhss)
                        f
                    bindrBlockM captures $ \captures' -> do
                        name <- newGName (tvName lhs)
                        fdef <- lowerFunDef freeLocalVars (Just lhs) name f
                        scribe outFunDefs [fdef]
                        closure <-
                            bindBlockM (emitNamed "closure")
                                =<< wrapInClosure Here (funDefGlobal fdef) captures'
                        pure $ mapTerm
                            (\closure' -> ((lhs, closure'), (freeLocalVars, captures')))
                            closure
            withVars binds $ do
                forM_ cs (uncurry populateCaptures)
                body' <- lowerExpr dest body
                pure (Low.Block stms1 () `thenBlock` body')
        Match es dt -> lowerMatch dest es dt
        Ction (variantIx, span, tconst, xs) -> lowerCtion dest variantIx span tconst xs
        Sizeof t ->
            toDest dest
                . Sized
                . operandToExpr
                =<< sized (fmap (litI64 . fromIntegral) . sizeof) (pure (litI64 0))
                =<< lowerType t
        Absurd _ -> toDest dest ZeroSized

    lowerExprToOperand :: Expr -> Lower (Low.Block (Sized Low.Operand))
    lowerExprToOperand e =
        bindBlockM (sized (fmap (mapTerm Sized) . emit) (pure (Low.Block [] ZeroSized)))
            =<< lowerExpr HereSized e

    lowerApp
        :: (Show d, Destination d)
        => d
        -> Expr
        -> [Expr]
        -> Lower (Low.Block (DestTerm d))
    lowerApp dest f as = case f of
        -- TODO: Handle this more elegantly. For example by exchanging Ction in Low for a
        --       Ctor, which behaves like a constructor or a function depending on
        --       context.
        Fun (params, (Ction (variantIx, span, tconst, xs), _rt))
            | map (Var NonVirt) params == xs -> lowerCtion dest variantIx span tconst as
        Fun (params, (body, _rt)) -> do -- Beta reduction
            (blk1, as') <- separateTerm . catBlocks <$> mapM lowerExprToOperand as
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
                    (Just (Low.OGlobal f), _, _, _) -> lowerApplicandGlobal f
                    (Just closure, _, _, _) -> lowerApplicandOperand closure
                    (_, Just f, _, _) -> lowerApplicandGlobal f
                    (_, _, Just (e, _), _) ->
                        pure (Low.Block [] (Nothing, Low.OExtern e))
                    (_, _, _, Just (selfLhs, selfCapts, selfRef)) | x == selfLhs ->
                        pure $ Low.Block [] (Just selfCapts, Low.OGlobal selfRef)
                    _ -> ice $ "lowerApplicand: variable not in any env: " ++ show x
            blk1 `thenBlockM` lowerApp' captures fConcrete
        _ -> do
            Low.Block stms (captures, fConcrete) <-
                bindBlockM lowerApplicandOperand
                =<< bindBlockM (emitNamed "closure")
                =<< lowerExpr Here f
            Low.Block stms () `thenBlockM` lowerApp' captures fConcrete
      where
        lowerApp' captures fConcrete = do
            let (params, ret) = asTFun (typeof fConcrete)
            Low.Block stms1 as' <-
                mapTerm catSized . catBlocks <$> mapM lowerExprToOperand as
            let args = maybe id (:) captures as'
            Low.Block stms2 args' <-
                catBlocks <$> zipWithM (removeIndirection . Low.paramType) params args
            thenBlockM (Low.Block (stms1 ++ stms2) ()) $ case ret of
                Low.RetVoid ->
                    Low.Block [Low.VoidCall fConcrete args'] ()
                        `thenBlockM` toDest dest ZeroSized
                Low.RetVal tret ->
                    toDest dest (Sized (Low.Expr (Low.Call fConcrete args') tret))
        lowerApplicandOperand closure = do
            Low.Block stms1 captures <- bindBlockM load =<< indexStruct 0 closure
            Low.Block stms2 fGeneric <- bindBlockM load =<< indexStruct 1 closure
            let (params, ret) = asTClosure (pointee (typeof closure))
            let tfConcrete = Low.TFun params ret
            Low.Block stms3 fConcrete <- emit
                $ Low.Expr (Low.Bitcast fGeneric tfConcrete) tfConcrete
            pure (Low.Block (stms1 ++ stms2 ++ stms3) (Just captures, fConcrete))
        lowerApplicandGlobal f = pure
            $ Low.Block [] (Just (Low.OConst (Low.Zero Low.VoidPtr)), Low.OGlobal f)

    lowerAppVirtual
        :: (Show d, Destination d)
        => d
        -> TypedVar
        -> [Expr]
        -> Lower (Low.Block (DestTerm d))
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
                ZeroSized -> toDest dest ZeroSized
                Sized tr' -> do
                    ta' <- fromSized <$> lowerType ta
                    tids' <- use tids
                    let isStackCast = \case
                            Low.TClosure _ _ -> True
                            Low.TConst tid ->
                                case snd (Seq.index tids' (fromIntegral tid)) of
                                    Low.DStruct _ -> True
                                    Low.DUnion _ -> True
                                    Low.DEnum _ -> False
                            _ -> False
                    if
                        | ta' == tr' -> lowerExpr dest a
                        | isStackCast ta' || isStackCast tr' -> do
                            (ptrTo, retVal) <- allocationAtDest dest Nothing tr'
                            Low.Block stms1 ptrFrom <- emit
                                (Low.Expr (Low.Bitcast ptrTo (Low.TPtr tr'))
                                          (Low.TPtr tr')
                                )
                            Low.Block stms2 () <- lowerExpr (There ptrFrom) a
                            pure (Low.Block (stms1 ++ stms2) retVal)
                        | otherwise -> do
                            a' <- bindBlockM emit =<< lowerExpr Here a
                            a' `bindrBlockM` \a'' -> toDest
                                dest
                                (Sized (Low.Expr (Low.Bitcast a'' tr') tr'))
            _ -> err
        "cast" -> case (tf, as) of
            (TFun [ta] tr, [a]) | (isInt ta || isFloat ta) && (isInt tr || isFloat tr) ->
                do
                    tr' <- fromSized <$> lowerType tr
                    (blk1, a') <- separateTerm <$> (bindBlockM emit =<< lowerExpr Here a)
                    blk2 <- toDest dest (Sized (Low.Expr (Low.Cast a' tr') tr'))
                    pure (blk1 `thenBlock` blk2)
            _ -> err
        "deref" -> lowerArgsHere >>= bindBlockM
            (\case
                [a] -> toDest dest (Sized (Low.Expr (Low.Load a) (pointee (typeof a))))
                _ -> err
            )
        "store" -> lowerArgsHere >>= bindBlockM
            (\case
                [a, b] ->
                    thenBlockM (Low.Block [Low.Store a b] ()) (toDest dest ZeroSized)
                _ -> err
            )
        _ -> ice $ "lowerAppVirtual: no builtin virtual function: " ++ f
      where
        arith op = lowerArgsHere >>= bindBlockM
            (\case
                [a, b] -> toDest dest (Sized (Low.Expr (op a b) (typeof a)))
                _ -> err
            )
        rel op = lowerArgsHere >>= bindBlockM
            (\case
                [a, b] -> toDest dest . Sized . Low.Expr (op a b) =<< typeBool
                _ -> err
            )
        lowerArgsHere = mapTerm catSized . catBlocks <$> mapM lowerExprToOperand as
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
    typeBool = Low.TConst . (Map.! ("Bool", [])) <$> use tconsts

    lowerLambda :: Destination d => d -> Fun -> Lower (Low.Block (DestTerm d))
    lowerLambda dest f = do
        (freeLocalVars, captures) <- precaptureFreeLocalVars Set.empty f
        Low.Block stms1 captures' <- populateCaptures freeLocalVars `bindBlockM` captures
        Low.Block stms2 captures'' <- emit
            (Low.Expr (Low.Bitcast captures' Low.VoidPtr) Low.VoidPtr)
        name <- newGName "fun"
        fdef <- lowerFunDef freeLocalVars Nothing name f
        scribe outFunDefs [fdef]
        Low.Block (stms1 ++ stms2) ()
            `thenBlockM` wrapInClosure dest (funDefGlobal fdef) captures''

    wrapInClosure
        :: Destination d
        => d
        -> Low.Global
        -> Low.Operand
        -> Lower (Low.Block (DestTerm d))
    wrapInClosure dest f@(Low.Global _ t) captures = do
        fGeneric <- emit (Low.Expr (Low.Bitcast (Low.OGlobal f) Low.VoidPtr) Low.VoidPtr)
        (ptr, x) <- allocationAtDest dest (Just "closure")
            $ uncurry Low.TClosure (asTFun t)
        bindrBlockM fGeneric $ \fGeneric' ->
            populateStruct [captures, fGeneric'] ptr <&> mapTerm (const x)

    lowerTag :: Span -> VariantIx -> Low.Operand
    lowerTag span variantIx = Low.OConst $ Low.CNat { Low.natWidth = tagBits span
                                                    , Low.natVal = fromIntegral variantIx
                                                    }

    populateStruct :: [Low.Operand] -> Low.Operand -> Lower (Low.Block Low.Operand)
    populateStruct vs dst = foldrM
        (\(i, v) rest ->
            indexStruct i dst
                >>= bindBlockM
                        (\member -> do
                            Low.Block stms v' <- removeIndirection (typeof member) v
                            pure $ Low.Block (stms ++ [Low.Store v' member]) ()
                        )
                <&> (`thenBlock` rest)
        )
        (Low.Block [] dst)
        (zip [0 ..] vs)

    lowerExprsInStruct :: [Expr] -> Low.Operand -> Lower (Low.Block ())
    lowerExprsInStruct es ptr = go 0 es
      where
        go _ [] = pure $ Low.Block [] ()
        go i (e : es) = do
            Low.Block stmsIndex subPtr <- indexStruct i ptr
            Low.Block stmsExpr result <- lowerExpr (ThereSized subPtr) e
            case result of
                Sized () ->
                    Low.Block (stmsIndex ++ stmsExpr) () `thenBlockM` go (i + 1) es
                ZeroSized -> Low.Block stmsExpr () `thenBlockM` go i es

    precaptureFreeLocalVars extraLocals (params, (body, _)) = do
        let params' = Set.fromList params
        freeLocalVars <- view localEnv <&> \locals -> Set.toList
            (Set.intersection (Set.difference (freeVars body) params')
                              (Set.union extraLocals (Map.keysSet locals))
            )
        (freeLocalVars, ) <$> if null freeLocalVars
            then pure (Low.Block [] (Low.OConst (Low.Zero Low.VoidPtr)))
            else do
                t <-
                    defineStruct "captures"
                    . map (first tvName)
                    =<< typedVarsSizedTypes freeLocalVars
                capturesSize <- sizeof t
                capturesGeneric <- emitNamed "captures"
                    =<< gcAlloc (litI64 (fromIntegral capturesSize))
                bindBlockM
                    (\c -> emitNamed
                        "captures"
                        (Low.Expr (Low.Bitcast c (Low.TPtr t)) (Low.TPtr t))
                    )
                    capturesGeneric

    typedVarsSizedTypes :: [TypedVar] -> Lower [(TypedVar, Low.Type)]
    typedVarsSizedTypes = mapMaybeM $ \v@(TypedVar _ t) -> lowerType t <&> \case
        Sized t' -> Just (v, t')
        ZeroSized -> Nothing

    gcAlloc :: Low.Operand -> Lower Low.Expr
    gcAlloc size =
        let fname = if noGC then "malloc" else "GC_malloc"
        in  fromLeft (ice "gcAlloc: (GC_)malloc was a void call")
                <$> callBuiltin fname [size]

    populateCaptures :: [TypedVar] -> Low.Operand -> Lower (Low.Block Low.Operand)
    populateCaptures freeLocals captures = do
        xs <- mapM (\var -> (Map.! var) <$> view localEnv) freeLocals
        populateStruct xs captures

    operandToExpr x = Low.Expr (Low.EOperand x) (typeof x)

    litI64 n = Low.OConst $ Low.CInt { Low.intWidth = 64, Low.intVal = n }

    lookupVar dest x = view (localEnv . to (Map.lookup x)) >>= \case
        Just l -> toDest dest (Sized (Low.mkEOperand l))
        Nothing -> view (globalEnv . to (Map.lookup x)) >>= \case
            Just f@(Low.Global _ (Low.TFun _ _)) ->
                wrapInClosure dest f (Low.OConst (Low.Zero Low.VoidPtr))
            Just g -> toDest dest (Sized (Low.mkEOperand (Low.OGlobal g)))
            Nothing -> view (externEnv . to (Map.lookup x)) >>= \case
                Just (_e, eWrapped) ->
                    wrapInClosure dest eWrapped (Low.OConst (Low.Zero Low.VoidPtr))
                Nothing -> view selfFun >>= \case
                    Just (selfLhs, selfCapts, f) | x == selfLhs ->
                        wrapInClosure dest f selfCapts
                    _ -> toDest dest ZeroSized

    lowerConst :: Const -> Lower Low.Operand
    lowerConst = \case
        Int n -> pure
            (Low.OConst (Low.CInt { Low.intWidth = 64, Low.intVal = fromIntegral n }))
        F64 x -> pure (Low.OConst (Low.F64 x))
        Str s -> internStr s <&> \s' -> Low.OGlobal s'

    internStr :: String -> Lower Low.Global
    internStr s = do
        tStr <- Low.TConst . (Map.! ("Str", [])) <$> use tconsts
        tArray <- Low.TConst . (Map.! ("Array", [TPrim (TNat 8)])) <$> use tconsts
        use (strLits . to (Map.lookup s)) >>= \case
            Just name -> pure (Low.Global name tStr)
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
                scribe
                    outConstDefs
                    [(nameInner, tInner, Low.CharArray bytes), (name, tStr, strRhs)]
                modifying strLits (Map.insert s name)
                pure (Low.Global name (Low.TPtr tStr))

    lowerStrEq :: Low.Operand -> Low.Operand -> Lower Low.Expr
    lowerStrEq s1 s2 =
        fromLeft (ice "lowerStrEq: str-eq was a void call")
            <$> callBuiltin "str-eq" [s1, s2]

    callBuiltin fname args = do
        es <- view externEnv
        let f = Low.OExtern . fst $ es Map.! TypedVar
                fname
                (Ast.builtinExterns Map.! fname)
        pure $ case returnee (typeof f) of
            Low.RetVal t -> Left (Low.Expr (Low.Call f args) t)
            Low.RetVoid -> Right (Low.VoidCall f args)

    lowerMatch
        :: forall d
         . (Show d, Destination d)
        => d
        -> [Expr]
        -> DecisionTree
        -> Lower (Low.Block (DestTerm d))
    lowerMatch dest matchees decisionTree = do
        Low.Block stms1 ms <- catBlocks <$> mapM lowerMatchee matchees
        Low.Block stms2 result <- lowerDecisionTree (topSelections ms) decisionTree
        pure (Low.Block (stms1 ++ stms2) result)
      where
        lowerMatchee m = lowerExpr HereSized m `bindrBlockM'` \case
            ZeroSized -> pure $ Low.Block [] ZeroSized
            Sized e -> mapTerm Sized <$> emitNamed "matchee" e

        topSelections :: [Sized Low.Operand] -> Map Low.Access Low.Operand
        topSelections xs = Map.fromList . catMaybes $ zipWith
            (\i x -> fmap (\x' -> (TopSel i (typeof x'), x')) (sizedMaybe x))
            [0 ..]
            xs

        lowerDecisionTree
            :: Map Low.Access Low.Operand
            -> DecisionTree
            -> Lower (Low.Block (DestTerm d))
        lowerDecisionTree selections = \case
            DLeaf (bs, e) -> do
                bs' <- mapMaybeM (\(x, a) -> fmap (x, ) . sizedMaybe <$> lowerAccess a) bs
                selectVarBindings selections bs'
                    `bindrBlockM'` \vars' -> withVars vars' (lowerExpr dest e)
            DSwitch _span selector cases default_ -> do
                selector' <- lowerSelector selector
                (m, selections') <- select selector' selections
                Low.Block stms tag <- bindrBlockM m $ \m' -> case typeof m' of
                    -- Either a pointer to a struct, representing a tagged union
                    Low.TPtr (Low.TConst _) -> indexStruct 0 m'
                    -- or an enum, which, as an integer, is its own "tag"
                    _ -> pure (Low.Block [] m')
                let litTagInt :: VariantIx -> Low.Const
                    litTagInt = case typeof tag of
                        Low.TNat { Low.tnatWidth = w } -> Low.CNat w . fromIntegral
                        t ->
                            ice
                                $ "lowerDecisionTree: litTagInt: unexpected type "
                                ++ show t
                cases' <- mapM
                    (bimapM (pure . litTagInt) (lowerDecisionTree selections'))
                    (Map.toAscList cases)
                default_' <- lowerDecisionTree selections' default_
                let result = branchToDest dest (Low.BSwitch tag cases' default_')
                pure $ Low.Block stms () `thenBlock` result
            DSwitchStr selector cases default_ -> do
                selector' <- lowerSelector selector
                ((block, matchee), selections') <-
                    first separateTerm <$> select selector' selections
                let
                    lowerCases = \case
                        [] -> lowerDecisionTree selections' default_
                        (s, dt) : cs -> do
                            s' <- internStr s
                            (block, isMatch) <- fmap separateTerm . emit =<< lowerStrEq
                                matchee
                                (Low.OGlobal s')
                            conseq <- lowerDecisionTree selections' dt
                            alt <- lowerCases cs
                            pure $ block `thenBlock` branchToDest
                                dest
                                (Low.BIf isMatch conseq alt)
                block `thenBlockM` lowerCases (Map.toAscList cases)

        -- Type checker wouldn't let us switch on something zero-sized, so we can
        -- safely unwrap the Sized
        lowerSelector selector = fromSized <$> lowerAccess selector

        select
            :: Low.Access
            -> Map Low.Access Low.Operand
            -> Lower (Low.Block Low.Operand, Map Low.Access Low.Operand)
        select selector selections = case Map.lookup selector selections of
            Just a -> pure (Low.Block [] a, selections)
            Nothing -> do
                (ba, selections') <- case selector of
                    TopSel _ _ ->
                        ice
                            $ "select: TopSel not in selections\nselector: "
                            ++ show selector
                            ++ "\nselections: "
                            ++ show selections
                    As x span' i _ts -> do
                        (ba', s') <- select x selections
                        ba'' <- bindrBlockM ba'
                            $ \a' -> asVariant a' span' (fromIntegral i)
                        pure (ba'', s')
                    Sel i _span x -> do
                        (a', s') <- select x selections
                        a'' <- bindrBlockM a' $ indexStruct (fromIntegral i)
                        pure (a'', s')
                    ADeref x -> do
                        (a', s') <- select x selections
                        a'' <- bindrBlockM a' load
                        pure (a'', s')
                pure (ba, Map.insert selector (Low.blockTerm ba) selections')

        -- Assumes matchee is of type pointer to tagged union
        asVariant matchee span variantIx = if span == 1
            then pure $ Low.Block [] matchee
            else do
                let
                    tidData = case typeof matchee of
                        Low.TPtr (Low.TConst tid) -> tid
                        _ -> ice "Lower.asVariant: type of matchee is not TPtr to TConst"
                let tvariant = Low.TPtr (Low.TConst (tidData + 2 + variantIx))
                -- Skip tag to get inner union
                indexStruct 1 matchee `bindrBlockM'` \union -> emit $ Low.Expr
                    (Low.EAsVariant union (fromIntegral variantIx))
                    tvariant

        selectVarBindings
            :: Map Low.Access Low.Operand
            -> [(TypedVar, Low.Access)]
            -> Lower (Low.Block [(TypedVar, Low.Operand)])
        selectVarBindings selections = fmap fst . foldlM
            (\(block1, selections) (x, access) -> do
                (block2, ss') <- select access selections
                pure (mapTerm (pure . (x, )) block2 <> block1, ss')
            )
            (Low.Block [] [], selections)

    lowerAccess :: Access -> Lower (Sized Low.Access)
    lowerAccess = \case
        TopSel i t -> mapSized (TopSel i) <$> lowerType t
        As a span vi vts ->
            mapSizedM (\a' -> As a' span vi <$> lowerSizedTypes vts) =<< lowerAccess a
        Sel i span a -> mapSized (Sel i span) <$> lowerAccess a
        ADeref a -> mapSized ADeref <$> lowerAccess a

    lowerCtion
        :: Destination d
        => d
        -> VariantIx
        -> Span
        -> TConst
        -> [Expr]
        -> Lower (Low.Block (DestTerm d))
    lowerCtion dest variantIx span tconst xs = do
        tconsts' <- use tconsts
        case Map.lookup tconst tconsts' of
            Nothing -> do
                blk <- catBlocks_ <$> mapM (lowerExpr Nowhere) xs
                blk `thenBlockM` toDest dest ZeroSized
            Just tidOuter -> do
                tids' <- use tids
                let (_, tdef) = Seq.index tids' (fromIntegral tidOuter)
                case tdef of
                    Low.DUnion _ -> ice "lowerExpr Ction: outermost TypeDef was a union"
                    Low.DEnum variants ->
                        let operand = Low.OConst $ Low.EnumVal
                                { Low.enumType = tidOuter
                                , Low.enumVariant = variants Vec.! fromIntegral variantIx
                                , Low.enumWidth = tagBits span
                                , Low.enumVal = fromIntegral variantIx
                                }
                        in  toDest dest . Sized $ Low.Expr (Low.EOperand operand)
                                                           (typeof operand)
                    Low.DStruct _ | span == 1 -> do
                        (ptr, retVal) <- allocationAtDest dest
                                                          Nothing
                                                          (Low.TConst tidOuter)
                        lowerExprsInStruct xs ptr <&> mapTerm (const retVal)
                    Low.DStruct _ | otherwise -> do
                        (ptr, retVal) <- allocationAtDest dest
                                                          Nothing
                                                          (Low.TConst tidOuter)
                        Low.Block stms1 tagPtr <- indexStruct 0 ptr
                        let stm2 = Low.Store (lowerTag span variantIx) tagPtr
                        let tidVariant = tidOuter + 2 + fromIntegral variantIx
                        Low.Block stms3 unionPtr <- indexStruct 1 ptr
                        Low.Block stms4 variantPtr <- emit $ Low.Expr
                            (Low.EAsVariant unionPtr variantIx)
                            (Low.TConst tidVariant)
                        Low.Block stms5 _ <- lowerExprsInStruct xs variantPtr
                        pure $ Low.Block (stms1 ++ stm2 : stms3 ++ stms4 ++ stms5) retVal

    -- Assumes that struct is kept on stack. Returns pointer to member.
    indexStruct :: Word -> Low.Operand -> Lower (Low.Block Low.Operand)
    indexStruct i x = do
        t <- Low.TPtr . (!! fromIntegral i) . Low.structMembers <$> getTypeStruct
            (pointee (typeof x))
        emit (Low.Expr (Low.EGetMember i x) t)

    catBlocks :: [Low.Block a] -> Low.Block [a]
    catBlocks = mconcat . map (mapTerm pure)

    catBlocks_ :: [Low.Block ()] -> Low.Block ()
    catBlocks_ = mconcat . map (mapTerm (const ()))

    withVars :: [(TypedVar, Low.Operand)] -> Lower a -> Lower a
    withVars vs ma = foldl (flip (uncurry withVar)) ma vs

    withVar :: TypedVar -> Low.Operand -> Lower a -> Lower a
    withVar lhs rhs = locally localEnv (Map.insert lhs rhs)

    builtinTypeDefs =
        -- closure: pointer to captures struct & function pointer, genericized
        [ ( "closure"
          , Low.DStruct Low.Struct { Low.structMembers = [Low.VoidPtr, Low.VoidPtr]
                                   , Low.structAlignment = wordsize
                                   , Low.structSize = wordsize * 2
                                   }
          )
        ]

    closureStruct = builtinType "closure"

    builtinType name = Low.TConst $ fromIntegral $ fromJust $ findIndex
        ((== name) . fst)
        builtinTypeDefs

    -- | How the different sorts of types are represented in Carth:
    --
    --   Zero sized types are treated like void in C -- you can't have a value of type
    --   void, but void can be used as something like a type in certain contexts, like
    --   function returns.
    --
    --   An Enum is represented as the smallest integer type that can fit all variants.
    --
    --   A Data is represented by a struct that consists of 2 members: an integer that can
    --   fit the variant index as well as "fill" the succeeding space (implied by
    --   alignment) until the second member starts, followed by the second member which is
    --   an array of integers with integer size equal to the alignment of the greatest
    --   aligned variant and array length equal to the smallest n that results in the
    --   array being of size >= the size of the largest sized variant.
    --
    --   The reason we must make sure to "fill" all space in the representing struct is
    --   that LLVM may essentially otherwise incorrectly assume that the space is unused
    --   and doesn't have to be considered when passing the type as an argument to a
    --   function.
    --
    --   The reason we fill it with values the size of the alignment instead of bytes is
    --   to not wrongfully signal to LLVM that the padding will be used as-is, and should
    --   be passed/returned in its own registers (or whatever exactly is going on). I just
    --   know from trial and error when debugging issues with how the representation of
    --   `(Maybe Int8)` affects how it is returned from a function. The intuitive
    --   definition (which indeed could be used for `Maybe` specifically without problems,
    --   since the only other variant is the non-data-carrying `None`) is `{i8,
    --   i64}`. Representing it instead with `{i64, i64}` (to make alignment-induced
    --   padding explicit, also this is how Rust represents it) works well -- it seems to
    --   be passed/returned in exactly the same way. However, if we represent it as `{i8,
    --   [7 x i8], i64}` or `{i8, [15 x i8], [0 x i64]}`: while having the same size and
    --   alignment, it is not returned in the same way (seeming instead to use an
    --   additional return parameter), and as such, a Carth function returning `(Maybe
    --   Int8)` represented as `{i8, [15 x i8], [0 x i64]}` is not ABI compatible with a
    --   Rust function returning `Maybe<i8>` represented as `{i64, i64}`.
    defineDatas :: Lower ()
    defineDatas = do
        (tids', _) <- mfix $ \result -> do
            tids .= fst result
            tconsts .= snd result
            bimap (Seq.fromList . (builtinTypeDefs ++)) Map.fromList . snd <$> foldlM
                (\(i, (env, ids)) (inst@(name, _), variants) -> do
                    def <- defineData i name variants
                    let (n, (env2, ids2)) = case def of
                            Nothing -> (0, ([], []))
                            Just (outer, inners) ->
                                ( 1 + fromIntegral (length inners)
                                , ((name, outer) : inners, [(inst, i)])
                                )
                    pure (i + n, (env ++ env2, ids ++ ids2))
                )
                (fromIntegral (length builtinTypeDefs), ([], []))
                (Map.toList datas)
        let tdefs' = Map.fromList $ zip (toList tids') [0 ..]
        tdefs .= tdefs'
      where
        defineData
            :: Low.TypeId
            -> String
            -> [(String, VariantTypes)]
            -> Lower (Maybe (Low.TypeDef', [Low.TypeDef]))
        defineData typeId0 name variants = do
            let (variantNames, variantTypess) = unzip variants
            -- Don't do lowerSizedTypes already here and match on its result. That would
            -- cause infinite recursion.
            case variantTypess of
                [] -> pure Nothing -- Uninhabited type
                [ts]
                    | any isSized ts
                    -> fmap (Just . (, [])) $ structDef =<< lowerSizedTypes ts
                    | otherwise
                    -> pure Nothing
                _ | not (any (any isSized) variantTypess) ->
                    pure $ Just (Low.DEnum (Vec.fromList variantNames), [])
                _ -> do
                    tss <- mapM lowerSizedTypes variantTypess
                    let tss' = filter (not . null) tss
                    aMax <- maximum <$> mapM alignmentofStruct tss'
                    sMax <- maximum <$> mapM sizeofStruct tss'
                    let variants' = Vec.fromList (zip variantNames [typeId0 + 2 ..])
                        sTag = variantsTagBits variants' :: Word
                        tag = if
                            | sTag <= 8 -> Low.TNat 8
                            | sTag <= 16 -> Low.TNat 16
                            | sTag <= 32 -> Low.TNat 32
                            | sTag <= 64 -> Low.TNat 64
                            | otherwise -> ice "Lower.defineData: tag > 64 bits"
                        unionId = typeId0 + 1
                    outerStruct <- structDef [tag, Low.TConst unionId]
                    let innerUnion =
                            (name ++ "_union", Low.DUnion $ Low.Union variants' sMax aMax)
                    variantStructs <- mapM
                        (secondM structDef)
                        (filter (not . null . snd) (zip variantNames tss))
                    pure $ Just (outerStruct, innerUnion : variantStructs)

        isSized :: Type -> Bool
        isSized = \case
            TPrim _ -> True
            TFun _ _ -> True
            TBox _ -> True
            TConst x -> any (any isSized . snd) (datas Map.! x)

    defineStruct :: String -> [(String, Low.Type)] -> Lower Low.Type
    defineStruct name members = do
        struct <- fmap (name, ) (structDef (map snd members))
        tdefs' <- use tdefs
        case Map.lookup struct tdefs' of
            Just tid -> pure (Low.TConst tid)
            Nothing -> do
                tid <- fromIntegral . Seq.length <$> use tids
                modifying tids (Seq.|> struct)
                modifying tdefs (Map.insert struct tid)
                pure (Low.TConst tid)

    structDef ts =
        liftM2 (Low.DStruct .* Low.Struct ts) (alignmentofStruct ts) (sizeofStruct ts)

    lowerParamTypes :: [Type] -> Lower [Low.Param ()]
    lowerParamTypes pts = catMaybes <$> mapM (toParam () <=< lowerType) pts

    toParam :: name -> Sized Low.Type -> Lower (Maybe (Low.Param name))
    toParam name = \case
        ZeroSized -> pure Nothing
        Sized t -> Just <$> sizedToParam name t

    sizedToParam name t = passByRef t <&> \case
        True -> Low.ByRef name t
        False -> Low.ByVal name t

    paramLocal :: Low.Param Low.LocalId -> Low.Local
    paramLocal = \case
        Low.ByVal name t -> Low.Local name t
        Low.ByRef name t -> Low.Local name (Low.TPtr t)

    toRet :: Lower name -> Sized Low.Type -> Lower (Maybe (Low.Param name), Low.Ret)
    toRet genName = \case
        ZeroSized -> pure (Nothing, Low.RetVoid)
        Sized t -> passByRef t >>= \case
            True -> genName <&> \name -> (Just (Low.ByRef name t), Low.RetVoid)
            False -> pure (Nothing, Low.RetVal t)

    lowerSizedTypes :: [Type] -> Lower [Low.Type]
    lowerSizedTypes = fmap catMaybes . mapM (fmap sizedMaybe . lowerType)

    -- TODO: Should respect platform ABI. For example wrt size of TNatSize on 32-bit
    --       vs. 64-bit platform.
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
            (outParam, ret) <- toRet (pure ()) =<< lowerType tret
            params <- lowerParamTypes tparams
            let captures = Low.ByVal () Low.VoidPtr
            pure (Sized (Low.TClosure (maybe id (:) outParam $ captures : params) ret))
        TBox t -> lowerType t <&> \case
            ZeroSized -> Sized Low.VoidPtr
            Sized t' -> Sized $ Low.TPtr t'
        TConst tc -> use tconsts <&> Map.lookup tc <&> \case
            Nothing -> ZeroSized
            Just ix -> Sized $ Low.TConst ix
      where
        intWidthCeil :: Word32 -> Sized Word
        intWidthCeil w = if
            | w == 0 -> ZeroSized
            | w <= 8 -> Sized 8
            | w <= 16 -> Sized 16
            | w <= 32 -> Sized 32
            | w <= 64 -> Sized 64
            | otherwise -> ice "Lower.lowerType: integral type larger than 64-bit"

    asTFun = \case
        Low.TFun params ret -> (params, ret)
        t -> ice $ "Lower.asTFun of non function type " ++ show t

    asTClosure = \case
        Low.TClosure params ret -> (params, ret)
        t -> ice $ "Lower.asTClosure of non closure type " ++ show t

    returnee = snd . asTFun

    getTypeStruct = \case
        Low.TConst i -> use tids <&> (Seq.!? fromIntegral i) <&> \case
            Just (_, Low.DStruct struct) -> struct
            _ -> ice "Low.getTypeStruct: TypeDef in tenv is not DStruct"
        Low.TClosure _ _ -> getTypeStruct closureStruct
        t -> ice $ "Low.getTypeStruct: type is not a TConst: " ++ show t

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
    passByRef :: Low.Type -> Lower Bool
    passByRef t = sizeof t <&> (> 2 * 8)

    sizeof = tidsHelper Low.sizeof
    sizeofStruct = tidsHelper Low.sizeofStruct
    alignmentofStruct = tidsHelper Low.alignmentofStruct

    tidsHelper f x = use tids <&> \tids' -> f (\tid -> tids' Seq.!? fromIntegral tid) x

pointee :: Low.Type -> Low.Type
pointee = \case
    Low.TPtr t -> t
    _ -> ice "Lower.pointee of non pointer type"

funDefGlobal :: Low.FunDef -> Low.Global
funDefGlobal Low.FunDef { Low.funDefName = x, Low.funDefParams = ps, Low.funDefRet = r }
    = Low.Global x (Low.TFun (map Low.dropParamName ps) r)

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
bindBlockM f (Low.Block stms1 a) =
    f a <&> \(Low.Block stms2 b) -> Low.Block (stms1 ++ stms2) b

bindrBlockM :: Monad m => Low.Block a -> (a -> m (Low.Block b)) -> m (Low.Block b)
bindrBlockM = flip bindBlockM

bindBlockM' :: Monad m => (a -> m (Low.Block b)) -> m (Low.Block a) -> m (Low.Block b)
bindBlockM' f ma = bindBlockM f =<< ma

bindrBlockM' :: Monad m => m (Low.Block a) -> (a -> m (Low.Block b)) -> m (Low.Block b)
bindrBlockM' = flip bindBlockM'

sized :: (a -> b) -> b -> Sized a -> b
sized f b = \case
    ZeroSized -> b
    Sized a -> f a

sizedMaybe :: Sized a -> Maybe a
sizedMaybe = \case
    ZeroSized -> Nothing
    Sized t -> Just t

fromSized :: Sized a -> a
fromSized = \case
    ZeroSized -> ice "Lower.fromSized: was ZeroSized"
    Sized x -> x

catSized :: [Sized a] -> [a]
catSized = mapMaybe sizedMaybe

-- Some types are kept on the stack for convenience when lowering, and may need to be
-- loaded to registers before being passed to function or put in a struct etc.
removeIndirection :: Low.Type -> Low.Operand -> Lower (Low.Block Low.Operand)
removeIndirection target x =
    if typeof x == Low.TPtr target then load x else pure (Low.Block [] x)

removeIndirectionE :: Low.Type -> Low.Expr -> Lower (Low.Block Low.Expr)
removeIndirectionE target x =
    if typeof x == Low.TPtr target then loadE x else pure (Low.Block [] x)

emit :: Low.Expr -> Lower (Low.Block Low.Operand)
emit = emitNamed "tmp"

emitNamed :: String -> Low.Expr -> Lower (Low.Block Low.Operand)
emitNamed _ (Low.Expr (Low.EOperand x) _) = pure (Low.Block [] x)
emitNamed name e = do
    name' <- newLName name
    let l = Low.Local name' (typeof e)
    pure (Low.Block [Low.Let l e] (Low.OLocal l))

load :: Low.Operand -> Lower (Low.Block Low.Operand)
load addr = emit $ Low.Expr (Low.Load addr) (pointee (typeof addr))

loadE :: Low.Expr -> Lower (Low.Block Low.Expr)
loadE addr =
    emit addr <&> mapTerm (\addr' -> Low.Expr (Low.Load addr') (pointee (typeof addr')))
