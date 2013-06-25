{-# LANGUAGE ImplicitParams #-}

module BFormula(BoolBOp(..),
                Formula(..),
                fdisj,
                fconj,
                fnot,
                fAtom,
                fVar,
                bopToBoolOp,
                boolOpToBOp,
                ptrFreeBExprToFormula) where

import Data.List
import Text.PrettyPrint

import Predicate
import Ops
import PP
import IVar
import ISpec
import IExpr
import IType

-- Logical operations
data BoolBOp = Conj 
             | Disj 
             | Impl
             | Equiv
             deriving (Eq)

bopToBoolOp :: BOp -> BoolBOp
bopToBoolOp And = Conj
bopToBoolOp Or  = Disj
bopToBoolOp Imp = Impl
bopToBoolOp Eq  = Equiv

instance PP BoolBOp where
    pp Conj  = text "&&"
    pp Disj  = text "||"
    pp Impl  = text "->"
    pp Equiv = text "<->"
    --pp = pp . boolOpToBOp

boolOpToBOp :: BoolBOp -> BOp
boolOpToBOp Conj  = And
boolOpToBOp Disj  = Or
boolOpToBOp Impl  = Imp
boolOpToBOp Equiv = Eq

-- Formula consists of predicates and boolean constants
-- connected with boolean connectors
data Formula = FTrue
             | FFalse
             | FPred  Predicate
             | FBinOp BoolBOp Formula Formula
             | FNot   Formula
             deriving (Eq)

instance PP Formula where
    pp FTrue             = text "true"
    pp FFalse            = text "false"
    pp (FPred p)         = parens $ pp p
    pp (FBinOp op f1 f2) = parens $ pp f1 <+> pp op <+> pp f2
    pp (FNot f)          = char '!' <> (parens $ pp f)

instance Show Formula where
    show = render . pp

fdisj :: [Formula] -> Formula
fdisj fs = case disjuncts'' of 
                [disjunct] -> disjunct
                _          -> foldl' (FBinOp Disj) (head disjuncts'') (tail disjuncts'')
    where disjuncts = filter (/= FFalse) fs
          disjuncts' = if (any (== FTrue) disjuncts) then [FTrue] else disjuncts
          disjuncts'' = case disjuncts' of 
                             [] -> [FFalse] 
                             _  -> disjuncts'

fconj :: [Formula] -> Formula
fconj fs = case conjuncts'' of
                [conjunct] -> conjunct
                _          -> foldl' (FBinOp Conj) (head conjuncts'') (tail conjuncts'')
    where conjuncts = filter (/= FTrue) fs
          conjuncts' = if (any (== FFalse) conjuncts) then [FFalse] else conjuncts
          conjuncts'' = case conjuncts' of 
                             [] -> [FTrue] 
                             _  -> conjuncts'

fnot :: Formula -> Formula
fnot FTrue  = FFalse
fnot FFalse = FTrue
fnot f      = FNot f

fAtom :: (?spec::Spec) => RelOp -> Term -> Term -> Formula
fAtom op t1 t2 = fAtom' op (termSimplify t1) (termSimplify t2)

fAtom' :: (?spec::Spec) => RelOp -> Term -> Term -> Formula
fAtom' REq  l r | l == r                         = FTrue
fAtom' REq  l r | isConstTerm l && isConstTerm r = if evalConstTerm l == evalConstTerm r then FTrue  else FFalse
fAtom' REq  l r | l < r                          = FPred $ PAtom REq l r
                | otherwise                      = FPred $ PAtom REq r l
fAtom' RNeq l r                                  = fnot $ fAtom' REq l r

fVar :: (?spec::Spec) => Formula -> [Var]
fVar FTrue            = []
fVar FFalse           = []
fVar (FPred p)        = concatMap termVar $ predTerm p
fVar (FBinOp _ f1 f2) = fVar f1 ++ fVar f2
fVar (FNot f)         = fVar f


-- Convert boolean expression without pointers to a formula
ptrFreeBExprToFormula :: (?spec::Spec) => Expr -> Formula
ptrFreeBExprToFormula e@(EVar _)                         = fAtom REq (exprToTerm e) TTrue
ptrFreeBExprToFormula   (EConst (BoolVal True))          = FTrue
ptrFreeBExprToFormula   (EConst (BoolVal False))         = FFalse
ptrFreeBExprToFormula e@(EField _ _)                     = fAtom REq (exprToTerm e) TTrue
ptrFreeBExprToFormula e@(EIndex _ _)                     = fAtom REq (exprToTerm e) TTrue
ptrFreeBExprToFormula   (EUnOp Not e)                    = fnot $ ptrFreeBExprToFormula e
ptrFreeBExprToFormula   (EBinOp op e1 e2) | isRelBOp op  = combineExpr (bopToRelOp op) e1 e2
ptrFreeBExprToFormula   (EBinOp op e1 e2) | isBoolBOp op = FBinOp (bopToBoolOp op) (ptrFreeBExprToFormula e1) (ptrFreeBExprToFormula e2)

combineExpr :: (?spec::Spec) => RelOp -> Expr -> Expr -> Formula
combineExpr REq  (EUnOp AddrOf e1) (EUnOp AddrOf e2) = combineAddrOfExpr e1 e2
combineExpr RNeq (EUnOp AddrOf e1) (EUnOp AddrOf e2) = fnot $ combineAddrOfExpr e1 e2
combineExpr op e1 e2 | typ e1 == Bool                = 
   case e1 of
       EConst (BoolVal True)  -> if op == REq then ptrFreeBExprToFormula e2 else fnot $ ptrFreeBExprToFormula e2
       EConst (BoolVal False) -> if op == REq then fnot $ ptrFreeBExprToFormula e2 else ptrFreeBExprToFormula e2
       _                      -> 
           case e2 of
                EConst (BoolVal True)  -> if op == REq then ptrFreeBExprToFormula e1 else fnot $ ptrFreeBExprToFormula e1
                EConst (BoolVal False) -> if op == REq then fnot $ ptrFreeBExprToFormula e1 else ptrFreeBExprToFormula e1
                _                      -> let f = FBinOp Equiv (ptrFreeBExprToFormula e1) (ptrFreeBExprToFormula e2)
                                          in if op == REq then f else fnot f
                     | otherwise                     = fAtom op (exprToTerm e1) (exprToTerm e2)

-- Two addrof expressions are equal if they are isomorphic and
-- array indices in matching positions in these expressions are equal.
combineAddrOfExpr :: (?spec::Spec) => Expr -> Expr -> Formula
combineAddrOfExpr (EVar n1)      (EVar n2)      | n1 == n2 = FTrue
combineAddrOfExpr (EVar n1)      (EVar n2)      | n1 /= n2 = FFalse
combineAddrOfExpr (EField e1 f1) (EField e2 f2) | f1 == f2 = combineAddrOfExpr e1 e2
                                                | f1 /= f2 = FFalse
combineAddrOfExpr (EIndex a1 i1) (EIndex a2 i2)            = fconj [combineAddrOfExpr a1 a2, combineExpr REq i1 i2]
combineAddrOfExpr (ESlice e1 s1) (ESlice e2 s2) | s1 == s2 = combineAddrOfExpr e1 e2
                                                | s1 /= s2 = FFalse
combineAddrOfExpr _              _                         = FFalse

