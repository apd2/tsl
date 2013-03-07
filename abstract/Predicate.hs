{-# LANGUAGE ImplicitParams #-}

module Predicate(PVarOps,
                 PDB,
                 bavarAVar,
                 AbsVar(..),
                 avarWidth,
                 avarIsPred,
                 avarCategory,
                 avarVar,
                 ArithUOp(..),
                 uopToArithOp,
                 arithOpToUOp,
                 ArithBOp(..),
                 bopToArithOp,
                 arithOpToBOp,
                 Term(..),
                 termWidth,
                 termCategory,
                 termVar,
                 termSimplify,
                 isConstTerm,
                 evalConstTerm,
                 isMemTerm,
                 RelOp(..),
                 bopToRelOp,
                 relOpToBOp,
                 Predicate(..),
                 predCategory,
                 predTerm,
                 predVar,
                 predToExpr,
                 exprToTerm,
                 termToExpr) where

import Text.PrettyPrint

import TSLUtil
import PP
import Ops
import ISpec
import IExpr
import IVar
import IType
import Interface hiding(getVar)
import Control.Monad.State
import Control.Monad.ST.Lazy

type PVarOps pdb s u = VarOps pdb (BAVar AbsVar AbsVar) s u
type PDB pdb s u     = StateT pdb (ST s)

bavarAVar :: BAVar AbsVar AbsVar -> AbsVar
bavarAVar (StateVar av _) = av
bavarAVar (LabelVar av _) = av
bavarAVar (OutVar   av _) = av

data AbsVar = AVarPred Predicate      -- predicate variable
            | AVarTerm Term           -- unabstracted Bool or Enum scalar variable
--            | AVarEnum String [I.Val]   -- variable with several interesting values
            deriving(Eq, Ord)

avarWidth :: (?spec::Spec) => AbsVar -> Int
avarWidth (AVarPred _) = 1
avarWidth (AVarTerm t) = termWidth t

avarCategory :: (?spec::Spec) => AbsVar -> VarCategory
avarCategory (AVarPred p) = predCategory p
avarCategory (AVarTerm t) = termCategory t

avarIsPred :: AbsVar -> Bool
avarIsPred (AVarPred _) = True
avarIsPred _            = False

avarVar :: (?spec::Spec) => AbsVar -> [Var]
avarVar (AVarPred p) = predVar p
avarVar (AVarTerm t) = termVar t

instance Show AbsVar where
    show (AVarPred p) = show p
    show (AVarTerm t) = show t

-- Objects with canonical form
class Canonical a where
    norm :: a -> a

-- Arithmetic operations
data ArithUOp = AUMinus 
              | ABNeg
              deriving (Eq,Ord)

uopToArithOp :: UOp -> ArithUOp
uopToArithOp UMinus = AUMinus
uopToArithOp BNeg   = ABNeg

arithOpToUOp :: ArithUOp -> UOp 
arithOpToUOp AUMinus = UMinus
arithOpToUOp ABNeg   = BNeg

data ArithBOp = ABAnd 
              | ABOr 
              | ABXor
              | ABConcat
              | APlus 
              | ABinMinus 
              | AMod
              | AMul
              deriving(Eq,Ord)

bopToArithOp :: BOp -> ArithBOp
bopToArithOp BAnd       = ABAnd       
bopToArithOp BOr        = ABOr 
bopToArithOp BXor       = ABXor
bopToArithOp BConcat    = ABConcat
bopToArithOp Plus       = APlus 
bopToArithOp BinMinus   = ABinMinus 
bopToArithOp Mod        = AMod
bopToArithOp Mul        = AMul

arithOpToBOp :: ArithBOp -> BOp
arithOpToBOp ABAnd      = BAnd       
arithOpToBOp ABOr       = BOr 
arithOpToBOp ABXor      = BXor
arithOpToBOp ABConcat   = BConcat
arithOpToBOp APlus      = Plus 
arithOpToBOp ABinMinus  = BinMinus 
arithOpToBOp AMod       = Mod
arithOpToBOp AMul       = Mul


-- Arithmetic (scalar) term
data Term = TVar    String
          | TSInt   Int Integer
          | TUInt   Int Integer
          | TEnum   String
          | TTrue
          | TAddr   Term
          | TField  Term String
          | TIndex  Term Term
          | TUnOp   ArithUOp Term
          | TBinOp  ArithBOp Term Term
          | TSlice  Term (Int,Int)
          deriving (Eq,Ord)

instance Canonical Term where
    norm = id

instance (?spec::Spec) => Typed Term where
    typ = typ . termToExpr

instance PP Term where
    pp = pp . termToExpr

instance Show Term where
    show = render . pp

isMemTerm :: (?spec::Spec) => Term -> Bool
isMemTerm (TVar n)     = varMem $ getVar n
isMemTerm (TField t _) = isMemTerm t
isMemTerm (TIndex t _) = isMemTerm t
isMemTerm (TSlice t _) = isMemTerm t
isMemTerm _        = False

termVar :: (?spec::Spec) => Term -> [Var]
termVar (TVar n)         = [getVar n]
termVar (TSInt _ _)      = []
termVar (TUInt _ _)      = []
termVar (TEnum _)        = []
termVar TTrue            = []
termVar (TAddr t)        = termVar t
termVar (TField t _)     = termVar t
termVar (TIndex a i)     = termVar a ++ termVar i
termVar (TUnOp _ t)      = termVar t
termVar (TBinOp _ t1 t2) = termVar t1 ++ termVar t2
termVar (TSlice t _)     = termVar t

isConstTerm :: (?spec::Spec) => Term -> Bool
isConstTerm = null . termVar

evalConstTerm :: Term -> Term
evalConstTerm = exprToTerm . EConst . evalConstExpr . termToExpr

termSimplify :: Term -> Term
termSimplify = exprToTerm . exprSimplify . termToExpr

termCategory :: (?spec::Spec) => Term -> VarCategory
termCategory t = if any ((==VarTmp) . varCat) $ termVar t
                    then VarTmp
                    else VarState

termWidth :: (?spec::Spec) => Term -> Int
termWidth t = case typ t of
                   Bool     -> 1
                   Enum n   -> bitWidth $ (length $ enumEnums $ getEnumeration n) - 1
                   (UInt w) -> w
                   (SInt w) -> w

-- Relational operations
data RelOp = REq
           | RNeq 
           | RLt 
           | RGt 
           | RLte 
           | RGte
           deriving (Eq,Ord)

instance PP RelOp where
    pp = pp . relOpToBOp

instance Show RelOp where
    show = render . pp

bopToRelOp :: BOp -> RelOp
bopToRelOp Eq  = REq
bopToRelOp Neq = RNeq
bopToRelOp Lt  = RLt
bopToRelOp Gt  = RGt
bopToRelOp Lte = RLte
bopToRelOp Gte = RGte

relOpToBOp :: RelOp -> BOp
relOpToBOp REq  = Eq
relOpToBOp RNeq = Neq
relOpToBOp RLt  = Lt
relOpToBOp RGt  = Gt
relOpToBOp RLte = Lte
relOpToBOp RGte = Gte

-- Predicates
data Predicate = PAtom {pOp :: RelOp, pTerm1 :: Term, pTerm2 :: Term} deriving (Eq, Ord)

instance PP Predicate where
    pp (PAtom op t1 t2) = pp t1 <> pp op <> pp t2

instance Show Predicate where
    show = render . pp

predTerm :: Predicate -> [Term]
predTerm (PAtom _ t1 t2) = [t1,t2]

predVar :: (?spec::Spec) => Predicate -> [Var]
predVar = concatMap termVar . predTerm

predCategory :: (?spec::Spec) => Predicate -> VarCategory
predCategory p = if any ((==VarTmp) . termCategory) $ predTerm p
                    then VarTmp
                    else VarState

-- Convert scalar expression without pointers and boolean operators to a term
exprToTerm :: Expr -> Term
exprToTerm = norm . exprToTerm'

exprToTerm' :: Expr -> Term
exprToTerm' (EVar n)                = TVar   n
exprToTerm' (EConst (BoolVal True)) = TTrue
exprToTerm' (EConst (SIntVal w i))  = TSInt w i
exprToTerm' (EConst (UIntVal w i))  = TUInt w i
exprToTerm' (EConst (EnumVal e))    = TEnum  e
exprToTerm' (EField s f)            = TField (exprToTerm' s) f
exprToTerm' (EIndex a i)            = TIndex (exprToTerm' a) (exprToTerm' i)
exprToTerm' (EUnOp AddrOf e)        = TAddr  (exprToTerm' e)
exprToTerm' (EUnOp op e)            = TUnOp  (uopToArithOp op) (exprToTerm' e)
exprToTerm' (EBinOp op e1 e2)       = TBinOp (bopToArithOp op) (exprToTerm' e1) (exprToTerm' e2)
exprToTerm' (ESlice e s)            = TSlice (exprToTerm' e) s

termToExpr :: Term -> Expr
termToExpr (TVar n)          = EVar   n
termToExpr (TUInt w i)       = EConst (UIntVal w i)
termToExpr (TSInt w i)       = EConst (SIntVal w i)
termToExpr (TEnum  e)        = EConst (EnumVal e)
termToExpr TTrue             = EConst (BoolVal True)
termToExpr (TAddr t)         = EUnOp  AddrOf (termToExpr t)
termToExpr (TField s f)      = EField (termToExpr s) f
termToExpr (TIndex a i)      = EIndex (termToExpr a) (termToExpr i)
termToExpr (TUnOp op t)      = EUnOp (arithOpToUOp op) (termToExpr t)
termToExpr (TBinOp op t1 t2) = EBinOp (arithOpToBOp op) (termToExpr t1) (termToExpr t2)
termToExpr (TSlice t s)      = ESlice (termToExpr t) s

predToExpr :: Predicate -> Expr
predToExpr (PAtom op t1 t2) = EBinOp (relOpToBOp op) (termToExpr t1) (termToExpr t2)
