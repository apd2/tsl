module Predicate() where

data Predicate = PAtom {pOp :: RelOp, p1 :: Term, p2 :: Term}

data Term = TVar    String
            TConst  Val
          | EField  Expr String
          | EIndex  Expr Expr
          | EUnOp   UOp Expr
          | EBinOp  BOp Expr Expr
          | ESlice  Expr Slice
          | EStruct String [Expr]


         | IntVal    Integer
         | StructVal (M.Map String TVal)
         | EnumVal   String
         | PtrVal    LExpr
         | ArrayVal  [TVal]


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

-- op is a relational operator
combineExpr :: BOp -> Expr -> Expr -> Formula
combineExpr op e1 e2
-- case 1: both sides are boolea atoms
-- case 2: one of the sides is a more complex boolean expression

type Cascade = Either [(Formula, Cascade)] Expr


exprToFormula e = exprToFormula $ EBinOp Eq e true

wps :: Formula -> Statement -> Formula
wps f (SAssume e) = FAnd f (exprToFormula e)
wps f (SAssign e1 e2) = 


wpt :: (?spec::Spec) => Formula -> Transition
