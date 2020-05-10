{-# LANGUAGE OverloadedStrings, LambdaCase, TupleSections, FlexibleContexts #-}

-- | Codegeneration related to external C function declarations
--
--   `extern` forms are translated pretty literally to extern declarations,
--   taking the C ABI into account when deciding whether to pass a ref on the
--   stack or in registers, etc. Further, ad wrapper-closure is generated around
--   the function, which translates the calling convention from C to whatever we
--   use internally (e.g. tailcc or fastcc), adds a dummy `captures` parameter
--   to make it compatible with all other function signatures, and finally it
--   adds currying.
--
--   One might think that simply declaring all function definitions and function
--   calls as being of the same "ccc" LLVM calling convention would allow us to
--   pass arguments and return results as we please, and everything will be
--   compatible? I sure did, however, that is not the case. To be compatible
--   with C FFIs, we also have to actually conform to the C calling convention,
--   which contains a bunch of details about how more complex types should be
--   passed and returned. Currently, we pass and return simple types by value,
--   and complex types by reference (param by ref, return via sret param).
--
--   See the definition of `passByRef` for up-to-date details about which types
--   are passed how.
module Extern (withExternSigs, genExterns, genBuiltins, callExtern) where

import LLVM.AST
import LLVM.AST.ParameterAttribute
import qualified LLVM.AST.Constant as LLConst
import Control.Monad.Writer
import qualified Data.Map as Map
import Lens.Micro.Platform (view, to)
import LLVM.AST.Typed
import qualified LLVM.AST.Type as LLType
import Data.Functor
import Data.Bifunctor

import Misc
import SrcPos
import qualified Monomorphic as M
import Monomorphic hiding (Type, Const)
import Gen


withExternSigs :: [(String, M.Type, SrcPos)] -> Gen' a -> Gen' a
withExternSigs es ga = do
    es' <- forM es $ \(name, t, _) -> do
        t' <- genType' t
        pure
            ( TypedVar name t
            , ConstantOperand $ LLConst.GlobalReference
                (LLType.ptr t')
                (mkName ("_wrapper_" ++ name))
            )
    augment env (Map.fromList es') ga

genExterns :: [(String, M.Type, SrcPos)] -> Gen' [Definition]
genExterns = fmap join . mapM genExtern

genExtern :: (String, M.Type, SrcPos) -> Gen' [Definition]
genExtern (name, t, pos) = do
    let (pts, rt) = uncurryType t
    when (null pts) $ ice "genExtern of non-function"
    let anon = mkName ""
    pts' <- mapM genType' pts
    ps <- forM pts' $ \pt' -> passByRef' pt' <&> \case
        True -> Parameter (LLType.ptr pt') anon [ByVal]
        False -> Parameter pt' anon []
    rt' <- genType' rt
    (rt'', ps') <- passByRef' rt' <&> \case
        True -> (LLType.void, Parameter (LLType.ptr rt') anon [SRet] : ps)
        False -> (rt', ps)
    let externDef = GlobalDefinition (simpleFunc (mkName name) ps' rt'' [] [])
    wrapperDefs <- genWrapper pos name rt' pts
    pure (externDef : wrapperDefs)

genWrapper :: SrcPos -> String -> Type -> [M.Type] -> Gen' [Definition]
genWrapper pos externName rt paramTs =
    case (zipWith (TypedVar . ("x" ++) . show) [1 :: Word ..] paramTs) of
        [] -> ice "genWrapper of empty param list"
        (firstParam : restParams) -> do
            let genCallExtern :: [TypedVar] -> Gen Val
                genCallExtern vars = do
                    ts <- mapM (\(TypedVar _ t) -> genType t) vars
                    vars' <- mapM lookupVar vars
                    as <- forM (zip vars' ts) $ \(v, t) -> passByRef t >>= \case
                        True -> fmap (, [ByVal]) (getVar v)
                        False -> fmap (, []) (getLocal v)
                    let ats = map (typeOf . fst) as
                    let fname = mkName externName
                    passByRef rt >>= \case
                        True -> do
                            out <- emitReg "out" (alloca rt)
                            let
                                f = ConstantOperand $ LLConst.GlobalReference
                                    (LLType.ptr $ FunctionType
                                        LLType.void
                                        (typeOf out : ats)
                                        False
                                    )
                                    fname
                            emitDo $ callVoid f ((out, [SRet]) : as)
                            pure (VVar out)
                        False ->
                            let
                                f = ConstantOperand $ LLConst.GlobalReference
                                    (LLType.ptr $ FunctionType rt ats False)
                                    fname
                                call = WithRetType
                                    (callVoid f as)
                                    (getFunRet (getPointee (typeOf f)))
                            in fmap VLocal (emitAnonReg call)
            let
                genWrapper' fvs = \case
                    [] -> genCallExtern fvs
                    (p : ps) -> do
                        pts <- mapM (\(TypedVar _ t) -> genType t) ps
                        let bt = foldr closureType rt pts
                        genLambda fvs p (genWrapper' (fvs ++ [p]) ps, bt)
            let fname = mkName ("_wrapper_f_" ++ externName)
            (f, gs) <- locallySet srcPos (Just pos) $
                genFunDef
                    ( fname
                    , []
                    , pos
                    , firstParam
                    , genWrapper' [firstParam] restParams
                    )
            let fref = LLConst.GlobalReference (LLType.ptr (typeOf f)) fname
            let captures = LLConst.Null (LLType.ptr typeUnit)
            let closure = litStruct [captures, fref]
            let closureDef = simpleGlobVar
                    (mkName ("_wrapper_" ++ externName))
                    (typeOf closure)
                    closure
            pure (GlobalDefinition closureDef : GlobalDefinition f : gs)

uncurryType :: M.Type -> ([M.Type], M.Type)
uncurryType = \case
    M.TFun a b -> first (a :) (uncurryType b)
    t -> ([], t)

passByRef :: Type -> Gen Bool
passByRef = lift . passByRef'

-- NOTE: This post is helpful:
--       https://stackoverflow.com/questions/42411819/c-on-x86-64-when-are-structs-classes-passed-and-returned-in-registers
--       Also, official docs:
--       https://software.intel.com/sites/default/files/article/402129/mpx-linux64-abi.pdf
--       particularly section 3.2.3 Parameter Passing (p18).
passByRef' :: Type -> Gen' Bool
passByRef' = \case
    NamedTypeReference x -> view (dataTypes . to (Map.lookup x)) >>= \case
        Just ts -> passByRef' (typeStruct ts)
        Nothing ->
            ice $ "passByRef': No dataType for NamedTypeReference " ++ show x
    -- Simple scalar types. They go in registers.
    VoidType -> pure False
    IntegerType _ -> pure False
    PointerType _ _ -> pure False
    FloatingPointType _ -> pure False
    -- Functions are not POD (Plain Ol' Data), so they are passed on the stack.
    FunctionType _ _ _ -> pure True
    -- TODO: Investigate how exactly SIMD vectors are to be passed when/if we
    --       ever add support for that in the rest of the compiler.
    VectorType _ _ -> pure True
    -- Aggregate types can either be passed on stack or in regs, depending on
    -- what they contain.
    t@(StructureType _ us) -> do
        size <- sizeof t
        if size > 16 then pure True else fmap or (mapM passByRef' us)
    ArrayType _ u -> do
        size <- sizeof u
        if size > 16 then pure True else passByRef' u
    -- N/A
    MetadataType -> ice "passByRef of MetadataType"
    LabelType -> ice "passByRef of LabelType"
    TokenType -> ice "passByRef of TokenType"
