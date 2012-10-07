module Predicate() where

data Predicate = PAtom {pOp :: RelOp, p1 :: Expr, p2 :: Expr}

pAtom :: RelOp -> Expr -> Expr -> Predicate
pAtom op l r = norm $ Predicate op l r

data RelOp = REq

data Formula = FBin BoolOp Formula Formula
             | FReplace  Predicate Formula
             | FPred     Predicate
             | FTrue
             | FFalse

data BoolOp = Conj | Disj | Impl

-- Objects with canonical form
class Canonical a where
    norm :: a -> a

instance Canonical Predicate

-- Convert _boolean_ expression to a formula
exprToFormula :: (?pdb::PredicateDB) => Expr -> Formula
exprToFormula (EConst (BoolVal True))  = FTrue
exprToFormula (EConst (BoolVal False)) = FFalse
exprToFormula (EUnOp  Not e)           = FNot $ exprToFormula e
exprToFormula (EBinOp op e1 e2) | elem op [Eq, Neq, Lt, Gt, Lte, Gte] = 
    combine op (expandPtr e1) (expandPtr e2)
exprToFormula (EBinOp And e1 e2)       = FBin Conj (exprToFormula e1) (exprToFormula e2)
exprToFormula (EBinOp Or e1 e2)        = FBin Disj (exprToFormula e1) (exprToFormula e2)
exprToFormula (EBinOp Imp e1 e2)       = FBin Impl (exprToFormula e1) (exprToFormula e2)


expandPtr :: Expr -> Cascade

combine :: BOp -> Cascade -> Cascade -> Formula

type Cascade = Either [(Formula, Cascade)] Expr


exprToFormula e = exprToFormula $ EBinOp Eq e true

wps :: Formula -> Statement -> Formula
wps f (SAssume e) = FAnd f (exprToFormula e)


wpt :: (?spec::Spec) => Formula -> Transition
