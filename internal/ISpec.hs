{-# LANGUAGE ImplicitParams #-}

module ISpec(Field(..),
             Type(..),
             Typed(..),
             Val(..),
             Enumeration(..),
             VarCategory(..),
             Var(..),
             Goal(..),
             Expr(..),
             scalars,
             disj,
             conj,
             true,
             false,
             (===),
             Loc,
             LocLabel(..),
             isDelayLabel,
             CFA,
             newCFA,
             cfaInitLoc,
             cfaErrLoc,
             cfaInsLoc,
             cfaLocLabel,
             cfaInsTrans,
             cfaInsTransMany,
             cfaInsTrans',
             cfaInsTransMany',
             Statement(..),
             (=:),
             nop,
             Transition(..),
             wp,
             Spec(..)) where

import Data.List
import Data.Maybe
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.Tree as G
import qualified Data.Map as M

import Util hiding (name)
import TSLUtil
import Common

data Field = Field String Type

instance Typed Field where
    typ (Field _ t) = t

data Type = Bool
          | SInt     Int
          | UInt     Int
          | Enum     String
          | Struct   [Field]
          | Ptr      Type
          | Array    Type Int

twidth :: Type -> Int
twidth (SInt w) = w
twidth (UInt w) = w
twidth _        = error "twidth undefined"

class Typed a where
    typ :: a -> Type

instance Typed Type where
    typ = id

typeWidth :: (Typed a) => a -> Int
typeWidth = twidth . typ

-- Value
data Val = BoolVal   Bool
         | SIntVal   Int Integer
         | UIntVal   Int Integer
         | EnumVal   String
         | PtrVal    LExpr

instance (?spec::Spec) => Typed Val where
    typ (BoolVal _)   = Bool
    typ (SIntVal w _) = SInt w
    typ (UIntVal w _) = UInt w
    typ (EnumVal n)   = Enum $ enumName $ getEnum n
    typ (PtrVal e)    = Ptr $ typ e

data Enumeration = Enumeration { enumName  :: String
                               , enumEnums :: [String]
                               }

data VarCategory = VarState
                 | VarTmp

data Var = Var { varMem  :: Bool
               , varCat  :: VarCategory
               , varName :: String
               , varType :: Type
               }

instance Typed Var where
    typ = varType

data Transition = Transition { tranFrom :: Loc
                             , tranTo   :: Loc
                             , tranCFA  :: CFA
                             }

data Goal = Goal { goalName :: String
                 , goalCond :: Expr
                 }

data Expr = EVar    String
          | EConst  Val
          | EField  Expr String
          | EIndex  Expr Expr
          | EUnOp   UOp Expr
          | EBinOp  BOp Expr Expr
          | ESlice  Expr Slice

instance (?spec::Spec) => Typed Expr where
    typ (EVar n)                               = typ $ getVar n
    typ (EConst v)                             = typ v
    typ (EField s f)                           = let Struct fs = typ s
                                                 in typ $ fromJust $ find (\(Field n _) -> n == f) fs 
    typ (EIndex a _)                           = t where Array t _ = typ a
    typ (EUnOp UMinus e)                       = SInt $ typeWidth e
    typ (EUnOp Not e)                          = Bool
    typ (EUnOp BNeg e)                         = typ e
    typ (EUnOp Deref e)                        = t where Ptr t = typ e
    typ (EUnOp AddrOf e)                       = Ptr $ typ e
    typ (EBinOp op e1 e2) | isRelBOp op        = Bool
                          | isBoolBOp op       = Bool
                          | isBitWiseBOp op    = typ e1
                          | op == BConcat      = UInt $ (typeWidth e1) + (typeWidth e2)
                          | elem op [Plus,Mul] = case (typ e1, typ e2) of
                                                         ((UInt w1), (UInt w2)) -> UInt $ max w1 w2
                                                         _                      -> SInt $ max (typeWidth e1) (typeWidth e2)
                          | op == BinMinus     = SInt $ max (typeWidth e1) (typeWidth e2)
                          | op == Mod          = typ e1
    typ (ESlice _ (l,h))                       = UInt $ h - l + 1


-- Extract all scalars from expression
scalars :: Expr -> Type -> [Expr]
scalars e (Struct fs)  = concatMap (\(Field n t) -> scalars (EField e n) t) fs
scalars e (Array  t s) = concatMap (\i -> scalars (EIndex e (EConst $ UIntVal (bitWidth $ s-1) $ fromIntegral i)) t) [0..s-1]
scalars e t            = [e]

(===) :: Expr -> Expr -> Expr
e1 === e2 = EBinOp Eq e1 e2

disj :: [Expr] -> Expr
disj [] = false
disj es = foldl' (\e1 e2 -> EBinOp Or e1 e2) (head es) (tail es)

conj :: [Expr] -> Expr
conj [] = false
conj es = foldl' (\e1 e2 -> EBinOp And e1 e2) (head es) (tail es)

true = EConst $ BoolVal True
false = EConst $ BoolVal False

type Slice = (Int, Int)

type LExpr = Expr

-- Atomic statement
data Statement = SAssume Expr
               | SAssign Expr Expr

(=:) :: Expr -> Expr -> Statement
(=:) e1 e2 = SAssign e1 e2

nop :: Statement
nop = SAssume $ true

-- Control-flow automaton
type Loc = G.Node
data LocLabel = LNone 
              | LPause Expr
              | LFinal 
type CFA = G.Gr LocLabel Statement

isDelayLabel :: LocLabel -> Bool
isDelayLabel (LPause _) = True
isDelayLabel LFinal     = True
isDelayLabel LNone      = False

newCFA :: Expr -> CFA
newCFA initcond = G.insNode (cfaInitLoc,LPause initcond) $ G.insNode (cfaErrLoc,(LPause false)) G.empty

cfaErrLoc :: Loc
cfaErrLoc = 0

cfaInitLoc :: Loc
cfaInitLoc = 1

cfaInsLoc :: LocLabel -> CFA -> (CFA, Loc)
cfaInsLoc lab cfa = (G.insNode (loc,lab) cfa, loc)
   where loc = (snd $ G.nodeRange cfa) + 1

cfaLocLabel :: Loc -> CFA -> LocLabel
cfaLocLabel loc cfa = fromJustMsg "cfaLocLabel" $ G.lab cfa loc

cfaInsTrans :: Loc -> Loc -> Statement -> CFA -> CFA
cfaInsTrans from to stat cfa = G.insEdge (from,to,stat) cfa

cfaInsTransMany :: Loc -> Loc -> [Statement] -> CFA -> CFA
cfaInsTransMany from to stats cfa = cfaInsTrans aft to nop cfa'
    where (cfa', aft) = foldl' (\(cfa, loc) stat -> let (cfa',loc') = cfaInsLoc LNone cfa
                                                    in (cfaInsTrans loc loc' stat cfa', loc'))
                               (cfa, from) stats

cfaInsTrans' :: Loc -> Statement -> CFA -> (CFA, Loc)
cfaInsTrans' from stat cfa = (cfaInsTrans from to stat cfa', to)
    where (cfa', to) = cfaInsLoc LNone cfa

cfaInsTransMany' :: Loc -> [Statement] -> CFA -> (CFA, Loc)
cfaInsTransMany' from stats cfa = (cfaInsTransMany from to stats cfa', to)
    where (cfa', to) = cfaInsLoc LNone cfa

data Spec = Spec { specEnum         :: [Enumeration]
                 , specVar          :: [Var]
                 , specCTran        :: [Transition]
                 , specUTran        :: [Transition]
                 , specWire         :: Transition
                 , specInit         :: Expr
                 , specGoal         :: [Goal] 
                 , specFair         :: [Expr]           -- sets of states f s.t. GF(-f)
                 }

getVar :: (?spec::Spec) => String -> Var
getVar n = fromJustMsg ("getVar: variable " ++ n ++ " not found") 
                       $ find ((==n) . varName) $ specVar ?spec 

getEnum :: (?spec::Spec) => String -> Enumeration
getEnum e = fromJustMsg ("getEnum: enumerator " ++ e ++ " not found")
                        $ find (elem e . enumEnums) $ specEnum ?spec

wp :: Expr -> [Transition] -> Expr
wp _ _ = error "Not implemented: wp"
