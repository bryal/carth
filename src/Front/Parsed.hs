{-# LANGUAGE DataKinds #-}

module Front.Parsed (module Front.Parsed, Const (..), TPrim(..), Type' (..), TConst') where

import qualified Data.Set as Set
import Data.Set (Set)
import Control.Arrow ((>>>))
import Data.Bifunctor

import Front.SrcPos
import FreeVars
import Front.TypeAst
import Front.Lexd (Const (..))

data Message = Warning SrcPos String
    deriving Show

data IdCase = Big | Small

newtype Id (case' :: IdCase) = Id (WithPos String)
    deriving (Show, Eq, Ord)

data TVar
    = TVExplicit (Id 'Small)
    | TVImplicit String
    deriving (Show, Eq, Ord)

type TConst = TConst' TVar
type Type = Type' TVar

type ClassConstraint = (String, [(SrcPos, Type)])

data Scheme = Forall SrcPos (Set TVar) (Set ClassConstraint) Type
    deriving (Show, Eq)

data Pat
    = PConstruction SrcPos (Id 'Big) [Pat]
    | PInt SrcPos Int
    | PStr SrcPos String
    | PVar (Id 'Small)
    | PBox SrcPos Pat
    -- TODO: Add special pattern for Lazy
    deriving Show

type FunPats = WithPos [Pat]

data Expr'
    = Lit Const
    | Var (Id 'Small)
    | App Expr [Expr]
    | If Expr Expr Expr
    | Let1 DefLike Expr
    | Let [DefLike] Expr
    | LetRec [Def] Expr
    | TypeAscr Expr Type
    | Match Expr [(Pat, Expr)]
    | Fun FunPats Expr
    | FunMatch [(FunPats, Expr)]
    | Ctor (Id 'Big)
    | Sizeof Type
    deriving (Show, Eq)

type Expr = WithPos Expr'

data Def = VarDef SrcPos (Id 'Small) (Maybe Scheme) Expr
         | FunDef SrcPos (Id 'Small) (Maybe Scheme) FunPats Expr
         | FunMatchDef SrcPos (Id 'Small) (Maybe Scheme) [(FunPats, Expr)]
    deriving (Show, Eq)

data DefLike = Def Def | Deconstr Pat Expr
    deriving (Show, Eq)

newtype ConstructorDefs = ConstructorDefs [(Id 'Big, [Type])]
    deriving (Show, Eq)

data TypeDef = TypeDef (Id 'Big) [Id 'Small] ConstructorDefs
    deriving (Show, Eq)

data Extern = Extern (Id 'Small) Type
    deriving (Show, Eq)

data Program = Program [Def] [TypeDef] [Extern]
    deriving (Show, Eq)


instance Eq Pat where
    (==) = curry $ \case
        (PConstruction _ x ps, PConstruction _ x' ps') -> x == x' && ps == ps'
        (PVar x, PVar x') -> x == x'
        _ -> False

instance FreeVars Def (Id 'Small) where
    freeVars = \case
        VarDef _ _ _ rhs -> freeVars rhs
        FunDef _ _ _ pats rhs ->
            Set.difference (freeVars rhs) (Set.unions (map bvPat (unpos pats)))
        FunMatchDef _ _ _ cs -> fvCases (map (first unpos) cs)

instance FreeVars DefLike (Id 'Small) where
    freeVars = \case
        Def d -> freeVars d
        Deconstr _ matchee -> freeVars matchee

instance FreeVars Expr (Id 'Small) where
    freeVars = fvExpr

instance HasPos (Id a) where
    getPos (Id x) = getPos x

instance HasPos Pat where
    getPos = \case
        PConstruction p _ _ -> p
        PInt p _ -> p
        PStr p _ -> p
        PVar v -> getPos v
        PBox p _ -> p


fvExpr :: Expr -> Set (Id 'Small)
fvExpr = unpos >>> fvExpr'
  where
    fvExpr' = \case
        Lit _ -> Set.empty
        Var x -> Set.singleton x
        App f as -> fvApp f as
        If p c a -> fvIf p c a
        Let1 b e -> Set.union (freeVars b) (Set.difference (freeVars e) (bvDefLike b))
        Let bs e -> foldr
            (\b fvs -> Set.union (freeVars b) (Set.difference fvs (bvDefLike b)))
            (freeVars e)
            bs
        LetRec ds e -> fvLet (unzip (map (\d -> (defLhs d, d)) ds)) e
        TypeAscr e _t -> freeVars e
        Match e cs -> fvMatch e cs
        Fun (WithPos _ pats) e -> Set.difference (freeVars e) (Set.unions (map bvPat pats))
        FunMatch cs -> fvCases (map (first unpos) cs)
        Ctor _ -> Set.empty
        Sizeof _t -> Set.empty
    bvDefLike = \case
        Def d -> Set.singleton (defLhs d)
        Deconstr pat _ -> bvPat pat

defLhs :: Def -> Id 'Small
defLhs = \case
    VarDef _ lhs _ _ -> lhs
    FunDef _ lhs _ _ _ -> lhs
    FunMatchDef _ lhs _ _ -> lhs

fvMatch :: Expr -> [(Pat, Expr)] -> Set (Id 'Small)
fvMatch e cs = Set.union (freeVars e) (fvCases (map (first pure) cs))

fvCases :: [([Pat], Expr)] -> Set (Id 'Small)
fvCases = Set.unions . map (\(ps, e) -> Set.difference (freeVars e) (Set.unions (map bvPat ps)))

bvPat :: Pat -> Set (Id 'Small)
bvPat = \case
    PConstruction _ _ ps -> Set.unions (map bvPat ps)
    PInt _ _ -> Set.empty
    PStr _ _ -> Set.empty
    PVar x -> Set.singleton x
    PBox _ p -> bvPat p

idstr :: Id a -> String
idstr (Id (WithPos _ x)) = x
