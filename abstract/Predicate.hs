{-# LANGUAGE ImplicitParams #-}

module Predicate(PVarOps,
                 PDB,
                 bavarAVar,
                 avarBAVar,
                 AbsVar(..),
                 avarWidth,
                 avarIsPred,
                 avarCategory,
                 avarVar,
                 avarTerms,
                 avarToExpr,
                 avarValToConst,
                 ArithUOp(..),
                 uopToArithOp,
                 arithOpToUOp,
                 ArithBOp(..),
                 bopToArithOp,
                 arithOpToBOp,
                 Term(..),
                 PTerm(..),
                 ptermTerm,
                 termWidth,
                 termCategory,
                 termVar,
                 isConstTerm,
                 --evalConstTerm,
                 RelOp(..),
                 bopToRelOp,
                 relOpToBOp,
                 relOpNeg,
                 relOpSwap,
                 PredOp(..),
                 relOpToPredOp,
                 predOpToBOp,
                 Predicate(..),
                 predCategory,
                 predTerm,
                 predVar,
                 predToExpr,
                 scalarExprToTerm,
                 valToTerm,
                 termToExpr,
                 ) where

import Text.PrettyPrint
import Data.List

import Util
import TSLUtil
import PP
import Ops
import ISpec
import IExpr
import IVar
import IType
import Interface hiding(getVar)
import Control.Monad.State
import Control.Monad.ST

type PVarOps pdb s u = VarOps pdb (BAVar AbsVar AbsVar) s u
type PDB pdb s u     = StateT pdb (ST s)

bavarAVar :: BAVar AbsVar AbsVar -> AbsVar
bavarAVar (StateVar av _) = av
bavarAVar (LabelVar av _) = av
bavarAVar (OutVar   av _) = av

avarBAVar :: (?spec::Spec) => AbsVar -> BAVar AbsVar AbsVar
avarBAVar av | avarCategory av == VarTmp   = LabelVar av (avarWidth av)
avarBAVar av | avarCategory av == VarState = StateVar av (avarWidth av)

data AbsVar = AVarPred Predicate   -- predicate variable
            | AVarEnum Term        -- unabstracted Enum scalar variable
            | AVarBool Term        -- unabstracted Bool variable
            | AVarInt  Term        -- unabstracted integral variable
--            | AVarEnum String [I.Val]   -- variable with several interesting values
            deriving(Eq, Ord)

avarWidth :: (?spec::Spec) => AbsVar -> Int
avarWidth (AVarPred _) = 1
avarWidth (AVarEnum t) = termWidth t
avarWidth (AVarBool _) = 1
avarWidth (AVarInt  t) = termWidth t

avarCategory :: (?spec::Spec) => AbsVar -> VarCategory
avarCategory (AVarPred p) = predCategory p
avarCategory (AVarEnum t) = termCategory t
avarCategory (AVarBool t) = termCategory t
avarCategory (AVarInt  t) = termCategory t

avarIsPred :: AbsVar -> Bool
avarIsPred (AVarPred _) = True
avarIsPred _            = False

avarVar :: (?spec::Spec) => AbsVar -> [Var]
avarVar (AVarPred p) = predVar p
avarVar (AVarEnum t) = termVar t
avarVar (AVarBool t) = termVar t
avarVar (AVarInt  t) = termVar t

avarTerms :: AbsVar -> [Term]
avarTerms = nub . avarTerms' 

avarTerms' :: AbsVar -> [Term]
avarTerms' (AVarPred p) = predTerm p
avarTerms' (AVarEnum t) = [t]
avarTerms' (AVarInt  t) = [t]
avarTerms' (AVarBool t) = [t]

avarToExpr :: (?spec::Spec) => AbsVar -> Expr
avarToExpr (AVarPred p) = predToExpr p
avarToExpr (AVarEnum t) = termToExpr t
avarToExpr (AVarBool t) = termToExpr t
avarToExpr (AVarInt  t) = termToExpr t

avarValToConst :: (?spec::Spec) => AbsVar -> Int -> Val
avarValToConst av i = case typ $ avarToExpr av of
                           Bool   -> if' (i==0) (BoolVal False) (BoolVal True)
                           UInt w -> UIntVal w (fromIntegral i)
                           SInt w -> SIntVal w (fromIntegral i)
                           Enum n -> EnumVal $ (enumEnums $ getEnumeration n) !! i


instance PP AbsVar where
    pp (AVarPred p) = pp p
    pp (AVarEnum t) = pp t
    pp (AVarBool t) = pp t
    pp (AVarInt  t) = pp t

instance Show AbsVar where
    show = render . pp

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

instance (?spec::Spec) => Typed Term where
    typ = typ . termToExpr

instance PP Term where
    pp = pp . termToExpr

instance Show Term where
    show = render . pp

termVar :: (?spec::Spec) => Term -> [Var]
termVar = exprVars . termToExpr

--evalConstTerm :: Term -> Term
--evalConstTerm = scalarExprToTerm . EConst . evalConstExpr . termToExpr

--termSimplify :: Term -> Term
--termSimplify = scalarExprToTerm . exprSimplify . termToExpr

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

-- Subset of terms that can be used in a predicate: int's, and pointers
-- (no structs, arrays, or bools)
data PTerm = PTInt Term
           | PTPtr Term
           deriving (Eq, Ord)

ptermTerm :: PTerm -> Term
ptermTerm (PTInt t) = t
ptermTerm (PTPtr t) = t

instance (?spec::Spec) => Typed PTerm where
    typ = typ . ptermTerm

instance PP PTerm where
    pp = pp . ptermTerm

instance Show PTerm where
    show = render . pp


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

relOpNeg :: RelOp -> RelOp
relOpNeg REq  = RNeq
relOpNeg RNeq = REq
relOpNeg RLt  = RGte
relOpNeg RGt  = RLte
relOpNeg RLte = RGt
relOpNeg RGte = RLt

-- swap sides
relOpSwap :: RelOp -> RelOp
relOpSwap REq  = REq
relOpSwap RNeq = RNeq
relOpSwap RLt  = RGt
relOpSwap RGt  = RLt
relOpSwap RLte = RGte
relOpSwap RGte = RLte

data PredOp = PEq
            | PLt
            | PLte
            deriving (Eq, Ord)

predOpToBOp :: PredOp -> BOp
predOpToBOp PEq  = Eq
predOpToBOp PLt  = Lt
predOpToBOp PLte = Lte

relOpToPredOp :: RelOp -> (Bool, PredOp)
relOpToPredOp REq  = (True,  PEq)
relOpToPredOp RNeq = (False, PEq)
relOpToPredOp RLt  = (True,  PLt)
relOpToPredOp RGt  = (False, PLt)
relOpToPredOp RLte = (True,  PLte)
relOpToPredOp RGte = (False, PLte)

instance PP PredOp where
    pp = pp . predOpToBOp

instance Show PredOp where
    show = render . pp

-- Predicates
data Predicate = PAtom {pOp :: PredOp, pTerm1 :: PTerm, pTerm2 :: PTerm} deriving (Eq, Ord)

instance PP Predicate where
    pp (PAtom op t1 t2) = pp t1 <> pp op <> pp t2

instance Show Predicate where
    show = render . pp

predTerm :: Predicate -> [Term]
predTerm (PAtom _ t1 t2) = [ptermTerm t1, ptermTerm t2]

predVar :: (?spec::Spec) => Predicate -> [Var]
predVar = nub . concatMap termVar . predTerm

predCategory :: (?spec::Spec) => Predicate -> VarCategory
predCategory p = if any ((==VarTmp) . termCategory) $ predTerm p
                    then VarTmp
                    else VarState

-- Convert scalar expression without pointer dereferences and boolean operators to a term
scalarExprToTerm :: Expr -> Term
scalarExprToTerm (EVar n)                = TVar n
scalarExprToTerm (EConst (BoolVal True)) = TTrue
scalarExprToTerm (EConst (SIntVal w i))  = TSInt w i
scalarExprToTerm (EConst (UIntVal w i))  = TUInt w i
scalarExprToTerm (EConst (EnumVal e))    = TEnum  e
scalarExprToTerm (EField s f)            = TField (scalarExprToTerm s) f
scalarExprToTerm (EIndex a i)            = TIndex (scalarExprToTerm a) (scalarExprToTerm i)
scalarExprToTerm (EUnOp AddrOf e)        = TAddr  (scalarExprToTerm e)
scalarExprToTerm (EUnOp op e)            = TUnOp  (uopToArithOp op) (scalarExprToTerm e)
scalarExprToTerm (EBinOp op e1 e2)       = TBinOp (bopToArithOp op) (scalarExprToTerm e1) (scalarExprToTerm e2)
scalarExprToTerm (ESlice e s)            = TSlice (scalarExprToTerm e) s

valToTerm :: Val -> Term
valToTerm = scalarExprToTerm . EConst

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

ptermToExpr :: PTerm -> Expr 
ptermToExpr = termToExpr . ptermTerm

isConstTerm :: Term -> Bool
isConstTerm = isConstExpr . termToExpr

predToExpr :: Predicate -> Expr
predToExpr (PAtom op t1 t2) = EBinOp (predOpToBOp op) (ptermToExpr t1) (ptermToExpr t2)
