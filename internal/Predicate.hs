{-# LANGUAGE ImplicitParams #-}

module Predicate(ArithUOp(..),
                 uopToArithOp,
                 arithOpToUOp,
                 ArithBOp(..),
                 bopToArithOp,
                 arithOpToBOp,
                 Term(..),
                 RelOp(..),
                 bopToRelOp,
                 relOpToBOp,
                 Predicate(..),
                 pAtom,
                 exprToTerm,
                 termToExpr) where

import Common
import ISpec
import IExpr

-- Arithmetic operations
data ArithUOp = AUMinus 
              | ABNeg
              deriving (Eq)

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
              deriving(Eq)

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
          deriving (Eq)

-- Relational operations
data RelOp = REq
           | RNeq 
           | RLt 
           | RGt 
           | RLte 
           | RGte
           deriving (Eq)

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
data Predicate = PAtom {pOp :: RelOp, p1 :: Term, p2 :: Term}

pAtom :: RelOp -> Term -> Term -> Predicate
pAtom op l r = norm $ PAtom op l r

-- Objects with canonical form
class Canonical a where
    norm :: a -> a

instance Canonical Predicate where
    norm p = error "Not implemented: norm Predicate"

-- Convert scalar expression without pointers and boolean operators to a term
exprToTerm :: Expr -> Term
exprToTerm (EVar n)               = TVar   n
exprToTerm (EConst (SIntVal w i)) = TSInt w i
exprToTerm (EConst (UIntVal w i)) = TUInt w i
exprToTerm (EConst (EnumVal e))   = TEnum  e
exprToTerm (EField s f)           = TField (exprToTerm s) f
exprToTerm (EIndex a i)           = TIndex (exprToTerm a) (exprToTerm i)
exprToTerm (EUnOp AddrOf e)       = TAddr  (exprToTerm e)
exprToTerm (EUnOp op e)           = TUnOp  (uopToArithOp op) (exprToTerm e)
exprToTerm (EBinOp op e1 e2)      = TBinOp (bopToArithOp op) (exprToTerm e1) (exprToTerm e2)
exprToTerm (ESlice e s)           = TSlice (exprToTerm e) s

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

