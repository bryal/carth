module LowPgms (emptyPgm, printPgm, factPgm, factLoopPgm) where

import Back.Low
import qualified Data.Vector as Vec

emptyPgm :: Program
emptyPgm = Program [emptyCarthInit, carth_main]
                   [installStackoverflowHandler]
                   []
                   (Vec.fromList [])
                   (Vec.fromList initNames)
    where carth_main = FunDef mainIx [] RetVoid (Block [] TRetVoid) [] (Vec.fromList [])

printPgm :: Program
printPgm = Program [emptyCarthInit, carth_main]
                   [installStackoverflowHandler, printIntDecl]
                   []
                   (Vec.fromList [])
                   (Vec.fromList initNames)
  where
    carth_main = FunDef
        mainIx
        []
        RetVoid
        (Block [VoidCall printIntOperand [OConst (CInt (LowInt 64 1337))]] TRetVoid)
        []
        (Vec.fromList [])

factPgm :: Program
factPgm = Program [emptyCarthInit, carth_main, factDef]
                  [installStackoverflowHandler, printIntDecl]
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
            [ Let result (Expr (Call fact [OConst (CInt (LowInt 64 5))]) (TInt 64))
            , VoidCall printIntOperand [OLocal result]
            ]
            TRetVoid
        )
        []
        (Vec.fromList ["result"])
    factDef = FunDef
        factIx
        [ByVal 1 (TInt 64)]
        (RetVal (TInt 64))
        (Block
            []
            (TBranch
                (BSwitch
                    (OLocal (Local 1 (TInt 64)))
                    [ ( CInt (LowInt 64 0)
                      , Block [] (TRetVal (mkEOperand (OConst (CInt (LowInt 64 1)))))
                      )
                    ]
                    (Block
                        [ Let
                            (Local 2 (TInt 64))
                            (Expr
                                (Sub (OLocal (Local 1 (TInt 64)))
                                     (OConst (CInt (LowInt 64 1)))
                                )
                                (TInt 64)
                            )
                        , Let
                            (Local 3 (TInt 64))
                            (Expr (Call fact [OLocal (Local 2 (TInt 64))]) (TInt 64))
                        , Let
                            result
                            (Expr
                                (Mul (OLocal (Local 1 (TInt 64)))
                                     (OLocal (Local 3 (TInt 64)))
                                )
                                (TInt 64)
                            )
                        ]
                        (TRetVal (mkEOperand (OLocal result)))
                    )
                )
            )
        )
        []
        (Vec.fromList ["result", "n", "tmp1", "tmp2"])
    result = Local 0 (TInt 64)
    fact = OGlobal (Global factIx (TFun [ByVal () (TInt 64)] (RetVal (TInt 64))))

factLoopPgm :: Program
factLoopPgm = Program [emptyCarthInit, carth_main]
                      [installStackoverflowHandler, printIntDecl]
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
            . flip Expr (TInt 64)
            . ELoop
            . Loop [(n, ci64 5), (prod, ci64 1)]
            $ Block
                  []
                  (LBranch
                      (BSwitch
                          (OLocal n)
                          [ ( CInt (LowInt 64 0)
                            , Block [] (Break (mkEOperand (OLocal prod)))
                            )
                          ]
                          (Block
                              [ Let prod' (Expr (Mul (OLocal n) (OLocal prod)) (TInt 64))
                              , Let n' (Expr (Sub (OLocal n) (ci64 1)) (TInt 64))
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
    result = Local 0 (TInt 64)
    prod = Local 1 (TInt 64)
    prod' = Local 2 (TInt 64)
    n = Local 3 (TInt 64)
    n' = Local 4 (TInt 64)

ci64 :: Integer -> Operand
ci64 = OConst . CInt . LowInt 64

installStackoverflowHandler :: ExternDecl
installStackoverflowHandler = ExternDecl "install_stackoverflow_handler" [] RetVoid

printIntOperand :: Operand
printIntOperand = OGlobal (Global printIntIx (TFun [ByVal () (TInt 64)] RetVoid))

printIntDecl :: ExternDecl
printIntDecl = ExternDecl "-print-int" [ByVal () (TInt 64)] RetVoid

mainIx, initIx, printIntIx :: Word
mainIx = 0
initIx = 1
printIntIx = 2

initNames :: [String]
initNames = ["carth_main", "carth_init", "-print-int"]

emptyCarthInit :: FunDef
emptyCarthInit = FunDef initIx [] RetVoid (Block [] TRetVoid) [] (Vec.fromList [])
        -- [ LL.Do (callNamed "install_stackoverflow_handler" [] LL.void)
        -- , LL.Do (callNamed "carth_init" [] LL.void)
        -- , LL.Do (callNamed "carth_main" [] LL.void)
