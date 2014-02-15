{-# LANGUAGE ImplicitParams #-}

module MkPredicate (mkPAtom, 
                    mkPRel) where

import Predicate
import BVSMT
import ISpec
import IExpr
import IType

-- All atoms must be created by this function
mkPAtom :: (?spec::Spec) => RelOp -> PTerm -> PTerm -> Either Bool (Bool, Predicate)
mkPAtom op pt1 pt2 = 
    case bvRelNormalise op (ptermTerm pt1) (ptermTerm pt2) of
         Left True                -> Left True
         Left False               -> Left False
         Right (pol, pop, t1, t2) -> Right $ (pol, PAtom pop pt1' pt2')
                                     where (pt1', pt2') = case pt1 of
                                                               PTPtr _ -> (PTPtr t1, PTPtr t2)
                                                               PTInt _ -> (PTInt t1, PTInt t2)

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
    where e' = termToExpr $ bvTermNormalise $ scalarExprToTerm e
