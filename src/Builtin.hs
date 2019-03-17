module Builtin
    ( schemes
    , values
    ) where

import Annot
import Ast (Const(..), Id(..))
import Data.Functor
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Val

schemes :: Map Id Scheme
schemes = Map.fromList (map (\(name, scm, _) -> (Id name, scm)) defs)

values :: Map String Val
values = Map.fromList (map (\(name, _, val) -> (name, val)) defs)

defs :: [(String, Scheme, Val)]
defs =
    [ ( "printInt"
      , Forall Set.empty (TFun typeInt typeUnit)
      , VFun (\v -> print (unwrapInt v) $> VConst Unit))
    , ( "+"
      , Forall Set.empty (TFun typeInt (TFun typeInt typeInt))
      , VFun (\a -> pure (VFun (\b -> pure (plus a b)))))
    ]

plus :: Val -> Val -> Val
plus a b = VConst (Int (unwrapInt a + unwrapInt b))
