{-# LANGUAGE ImplicitParams #-}

module Abstract.MkPredicate (mkPRel,
                    scalarExprToTerm,
                    scalarExprToTerm',
                    termPad,
                    valToTerm
                    ) where

import Ops
import Abstract.Predicate
import Solver.BVSMT
import Internal.ISpec
import Internal.IExpr
import Internal.IType

-- Assumes that all dereference operations have already been expanded
mkPRel :: (?spec::Spec) => String -> [Expr] -> Predicate
mkPRel r as = PRel r $ map exprNormalise as

-- Apply bvTermNormalise to scalar sub-terms of the expression
exprNormalise :: (?spec::Spec) => Expr -> Expr
exprNormalise = mapExpr exprNormalise'

exprNormalise' :: (?spec::Spec) => Expr -> Expr
exprNormalise' e = case typ e of
                        UInt _ -> e'
                        SInt _ -> e'
                        _      -> e
    where e' = termToExpr $ scalarExprToTerm e

-- Convert scalar expression without pointer dereferences and boolean operators to a term
scalarExprToTerm :: (?spec::Spec) => Expr -> Term
scalarExprToTerm e = bvTermNormalise $ scalarExprToTerm' e

scalarExprToTerm' :: Expr -> Term
scalarExprToTerm' (EVar n)                = TVar n
scalarExprToTerm' (EConst (BoolVal True)) = TTrue
scalarExprToTerm' (EConst (SIntVal w i))  = TSInt w i
scalarExprToTerm' (EConst (UIntVal w i))  = TUInt w i
scalarExprToTerm' (EConst (EnumVal e))    = TEnum  e
scalarExprToTerm' (EField s f)            = TField (scalarExprToTerm' s) f
scalarExprToTerm' (EIndex a i)            = TIndex (scalarExprToTerm' a) (scalarExprToTerm' i)
scalarExprToTerm' (EUnOp AddrOf e)        = TAddr  (scalarExprToTerm' e)
scalarExprToTerm' (EUnOp op e)            = TUnOp  (uopToArithOp op) (scalarExprToTerm' e)
scalarExprToTerm' (EBinOp op e1 e2)       = TBinOp (bopToArithOp op) (scalarExprToTerm' e1) (scalarExprToTerm' e2)
scalarExprToTerm' (ESlice e s)            = TSlice (scalarExprToTerm' e) s

valToTerm :: Val -> Term
valToTerm = scalarExprToTerm' . EConst

termPad :: (?spec::Spec) => Int -> Term -> Term
termPad i = scalarExprToTerm . exprPad i . termToExpr
