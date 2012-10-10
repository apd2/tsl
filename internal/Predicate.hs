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

-- Arithmetic (scalar) term
data Term = TVar    String
          | TInt    Integer
          | TEnum   String
          | TTrue
          | TAddr   Term
          | TField  Term String
          | TIndex  Term Term
          | TUnOp   ArithUOp Term
          | TBinOp  ArithBOp Term Term
          | TSlice  Term (Int,Int)

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
             | FReplace  Formula Predicate Formula


-- Intermediate data structure that represents the value of
-- an arithmetic expression depending on pointer predicates
-- or other conditions
data Cascade a = CasTree  [(Formula, Cascade a)] 
               | CasLeaf a

ctrue :: Cascade Expr
ctrue = CasLeaf true

-- Expand each pointer dereference operation in the expression
-- using predicates in the DB.
exprExpandPtr :: (?pdb::PredicateDB) => Expr -> Cascade Expr

-- Compare two cascades
combine :: RelOp -> Cascade Expr -> Cascade Expr -> Formula
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
updateFormStat :: Formula -> Statement -> Formula
updateFormStat f (SAssume e)     = FBinOp Conj f (exprToFormula e)
updateFormStat f (SAssign e1 e2) = foldl' (\f (e1,e2) -> updateFormAsn e1 e2 f) f $ zip sc1 sc2
    where sc1 = exprScalars e1 
          sc2 = exprScalars e2

-- Formula update by assignment statement
updateFormAsn :: Expr -> Expr -> Formula -> Formula
updateFormAsn lhs rhs f = 
    foldl' (\f p -> FReplace f p (updatePredAsn lhs rhs p)) f $ formPreds f

-- Predicate update by assignment statement
updatePredAsn :: Expr -> Expr -> Predicate -> Formula
updatePredAsn lhs rhs p = pSubstScalCas p sc'
    sc' = map (updateScalAsn lhs rhs) $ pScalars p
 
-- Takes lhs and rhs of assignment statement and a term
-- Computes possible overlaps of the lhs with the term and
-- corresponding next-state values of the term expressed as concatenation 
-- of slices of the rhs and the original term.
updateScalAsn :: Expr -> Expr -> Term -> Cascade [Expr]
updateScalAsn e                rhs (TSlice t s) = casSlice (updateScalAsn e rhs t) s
updateScalAsn (ESlice e (l,h)) rhs t            = 
    casMap (\b -> if b
                     then (if l == 0 then [] else [termToExpr $ TSlice t (0,l-1)] ++
                           [ESlice rhs (l,h)] ++
                           if h == w - 1 then [] else [termToExpr $ TSlice t (h+1, w - 1)])
                     else [termToExpr t]) 
           $ lhsTermEq e t
    where w = exprWidth e
updateScalAsn lhs              rhs t            = 
    casMap (\b -> if b then [rhs] else [termToExpr t]) $ lhsTermEq lhs t


-- Takes lhs expression and a term and computes the condition 
-- when the expression is a synonym of the term.
lhsTermEq :: Expr -> Term -> Cascade Bool
lhsTermEq (EVar n1)       (TVar n2)        | n1 == n2 = CasLeaf True
lhsTermEq (EField e f1)   (TField t f2)    | f1 == f2 = lhsTermEq e t
lhsTermEq (EIndex ae ie)  (TIndex at it)              = 
    casMap (\b -> if b 
                     then case exprToFormula $ (termToExpr it) === ie of
                               FTrue  -> CasLeaf True
                               FFalse -> CasLeaf False
                               f      -> CasTree [(f, CasLeaf True), (FNot f, CasLeaf False)]
                     else CasLeaf False)
           $ lhsTermEq ae at
lhsTermEq (EUnOp Deref e) t                 | typeMatch etyp ttyp && isMemTerm t = 
    case exprToFormula $ e === EUnOp AddrOf (termToExpr t) of
         FTrue  -> CasLeaf True
         FFalse -> CasLeaf False
         f      -> CasTree [(f, CasLeaf True), (FNot f, CasLeaf False)]
    where Ptr etyp = typ e
          ttyp     = typ t
lhsTermEq _              _                           = CasLeaf False


-- Extract scalar terms from predicate
pScalars :: Predicate -> [Term]

-- Substitute all scalar terms in a predicate with cascades of scalar expressions.
pSubstScalCas :: Predicate -> [Cascade [Expr]] -> Formula
