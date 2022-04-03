module LowPgms (emptyPgm, printPgm, factPgm, factLoopPgm) where

import Back.Low
import qualified Data.Vector as Vec

emptyPgm :: Program
emptyPgm = Program [empty_carth_init, carth_main]
                   [install_stackoverflow_handler]
                   []
                   (Vec.fromList [])
                   (Vec.fromList initNames)
    where carth_main = FunDef mainIx [] RetVoid (Block [] TRetVoid) [] (Vec.fromList [])

printPgm :: Program
printPgm = Program [empty_carth_init, carth_main]
                   [install_stackoverflow_handler, printIntDecl]
                   []
                   (Vec.fromList [])
                   (Vec.fromList initNames)
  where
    carth_main = FunDef
        mainIx
        []
        RetVoid
        (Block [VoidCall printIntOperand [OConst (CInt (I64 1337))]] TRetVoid)
        []
        (Vec.fromList [])

factPgm :: Program
factPgm = Program [empty_carth_init, carth_main, factDef]
                  [install_stackoverflow_handler, printIntDecl]
                  []
                  (Vec.fromList [])
                  (Vec.fromList (initNames ++ ["fact"]))
  where
    factIx = fromIntegral (0 + length initNames)
    carth_main = FunDef
        mainIx
        []
        RetVoid
        (Block
            [ Let result (Expr (Call fact [OConst (CInt (I64 5))]) TI64)
            , VoidCall printIntOperand [OLocal result]
            ]
            TRetVoid
        )
        []
        (Vec.fromList ["result"])
    factDef = FunDef
        factIx
        [ByVal 1 TI64]
        (RetVal TI64)
        (Block
            []
            (TBranch
                (Switch
                    (Local 1 TI64)
                    [(CInt (I64 0), Block [] (TRetVal (OConst (CInt (I64 1)))))]
                    (Block
                        [ Let
                            (Local 2 TI64)
                            (Expr
                                (Sub (OLocal (Local 1 TI64)) (OConst (CInt (I64 1))))
                                TI64
                            )
                        , Let (Local 3 TI64)
                              (Expr (Call fact [OLocal (Local 2 TI64)]) TI64)
                        , Let
                            result
                            (Expr
                                (Mul (OLocal (Local 1 TI64)) (OLocal (Local 3 TI64)))
                                TI64
                            )
                        ]
                        (TRetVal (OLocal result))
                    )
                )
            )
        )
        []
        (Vec.fromList ["result", "n", "tmp1", "tmp2"])
    result = Local 0 TI64
    fact = OGlobal (Global factIx (TFun [ByVal () TI64] (RetVal TI64)))

factLoopPgm :: Program
factLoopPgm = Program [empty_carth_init, carth_main]
                      [install_stackoverflow_handler, printIntDecl]
                      []
                      (Vec.fromList [])
                      (Vec.fromList initNames)
  where
    carth_main = FunDef
        mainIx
        []
        RetVoid
        (Block
            [ Let result
            $ flip Expr TI64
            $ Loop [(n, ci64 5), (prod, ci64 1)] TI64
            $ Block
                  []
                  (LBranch
                      (Switch
                          n
                          [(CInt (I64 0), Block [] (Break (OLocal prod)))]
                          (Block
                              [ Let prod' (Expr (Mul (OLocal n) (OLocal prod)) TI64)
                              , Let n' (Expr (Sub (OLocal n) (ci64 1)) TI64)
                              ]
                              (Continue [OLocal n', OLocal prod'])
                          )
                      )
                  )
            , VoidCall printIntOperand [OLocal result]
            ]
            TRetVoid
        )
        []
        (Vec.fromList ["result", "prod", "prod_next", "n", "n_next"])
    result = Local 0 TI64
    prod = Local 1 TI64
    prod' = Local 2 TI64
    n = Local 3 TI64
    n' = Local 4 TI64

ci64 :: Int -> Operand
ci64 = OConst . CInt . I64

install_stackoverflow_handler :: ExternDecl
install_stackoverflow_handler = ExternDecl "install_stackoverflow_handler" [] RetVoid

printIntOperand :: Operand
printIntOperand = OGlobal (Global printIntIx (TFun [ByVal () TI64] RetVoid))

printIntDecl :: ExternDecl
printIntDecl = ExternDecl "-print-int" [ByVal () TI64] RetVoid

mainIx, initIx, printIntIx :: Word
mainIx = 0
initIx = 1
printIntIx = 2

initNames :: [String]
initNames = ["carth_main", "carth_init", "-print-int"]

empty_carth_init :: FunDef
empty_carth_init = FunDef initIx [] RetVoid (Block [] TRetVoid) [] (Vec.fromList [])
        -- [ LL.Do (callNamed "install_stackoverflow_handler" [] LL.void)
        -- , LL.Do (callNamed "carth_init" [] LL.void)
        -- , LL.Do (callNamed "carth_main" [] LL.void)
