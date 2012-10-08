{-# LANGUAGE ImplicitParams #-}

module Predicate() where

import Common
import ISpec

-- Arithmetic operations
data ArithUOp = AUMinus 
              | ABNeg
              deriving (Eq)

data ArithBOp = ABAnd 
              | ABOr 
              | ABXor
              | APlus 
              | ABinMinus 
              | AMod
              | AMul
              deriving(Eq)

-- Arithmetic term
data Term = TVar    String
          | TInt    Integer
          | TEnum   String
          | TTrue
          | TAddr   Term
          | TField  Term String
          | TIndex  Term Term
          | TUnOp   ArithUOp Term
          | TBinOp  ArithBOp Term Term
          | TSlice  Term (Term,Term)

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

-- Predicates
data Predicate = PAtom {pOp :: RelOp, p1 :: Term, p2 :: Term}

pAtom :: RelOp -> Term -> Term -> Predicate
pAtom op l r = norm $ PAtom op l r

-- Objects with canonical form
class Canonical a where
    norm :: a -> a

instance Canonical Predicate where

-- Predicate database
type PredicateDB = [Predicate]

-- Logical operations
data BoolOp = Conj 
            | Disj 
            | Impl
            | Equiv
            deriving (Eq)

-- Formula consists of predicates and boolean constants
-- connected with boolean connectors
data Formula = FTrue
             | FFalse
             | FPred     Predicate
             | FBinOp    BoolOp Formula Formula
             | FNot      Formula
             | FReplace  Predicate Formula


-- Intermediate data structure that represents the value of
-- an arithmetic expression depending on pointer predicates
-- or other conditions
data Cascade = CasCase [(Formula, Cascade)] 
             | CasTerm Expr

ctrue :: Cascade
ctrue = CasTerm TTrue

-- Convert arithmetic expression to arithmetic term
exprExpandPtr :: (?pdb::PredicateDB) => Expr -> Cascade
exprExpandPtr e = error "Not implemented: exprExpandPtr" 

-- Compare two cascades
combine :: RelOp -> Cascade -> Cascade -> Formula
combine op c1 c2 = error "Not implemented: combine"

-- op is a relational operator
--combineExpr :: BOp -> Expr -> Expr -> Formula
--combineExpr op e1 e2
-- case 1: both sides are boolea atoms
-- case 2: one of the sides is a more complex boolean expression


-- Convert boolean expression to a formula
exprToFormula :: (?pdb::PredicateDB) => Expr -> Formula
exprToFormula e@(EVar   _)             = combine REq (exprExpandPtr e) ctrue
exprToFormula e@(EField _ _)           = combine REq (exprExpandPtr e) ctrue
exprToFormula e@(EIndex _ _)           = combine REq (exprExpandPtr e) ctrue
exprToFormula (EConst (BoolVal True))  = FTrue
exprToFormula (EConst (BoolVal False)) = FFalse
exprToFormula (EUnOp  Not e)           = FNot $ exprToFormula e
exprToFormula (EBinOp op e1 e2) | elem op [Eq, Neq, Lt, Gt, Lte, Gte] = 
                                         combine (bopToRelOp op) (exprExpandPtr e1) (exprExpandPtr e2)
exprToFormula (EBinOp And e1 e2)       = FBinOp Conj (exprToFormula e1) (exprToFormula e2)
exprToFormula (EBinOp Or e1 e2)        = FBinOp Disj (exprToFormula e1) (exprToFormula e2)
exprToFormula (EBinOp Imp e1 e2)       = FBinOp Impl (exprToFormula e1) (exprToFormula e2)

-- Weakest precondition of a formula wrt a statement
wps :: Formula -> Statement -> Formula
wps f (SAssume e)     = FBinOp Conj f (exprToFormula e)
wps f (SAssign e1 e2) = 


--wp(e1 op e2, e3:=e4)  = wp(e1, e3:=e4)  op wp(e2, e3:=e4)
--
--wp(e, e3:=e4) -> -- find which part of e might be changed and
--                 -- to what subexpressions of e4
--                 overlap(e, e3, e4)::Cascade Expr
--                 -- for each element in the cascade,
--                 -- expand the RHS
--                 rhs -> 
--
--combinerhs :: (Expr, Expr) -> Cascade Formula
---- expand pointers in order
--

---- Weakest precondition of a formula wrt a transition
--wpt :: (?spec::Spec) => Formula -> Transition -> Formula
--
