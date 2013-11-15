{-# LANGUAGE ImplicitParams #-}

module MkPredicate (mkPAtom, 
                    mkPRel) where

import Predicate
import BVSMT
import ISpec
import IExpr

-- All atoms must be created by this function
mkPAtom :: (?spec::Spec) => RelOp -> PTerm -> PTerm -> Either Bool Predicate
mkPAtom op pt1 pt2 = 
    case bvRelNormalise op (ptermTerm pt1) (ptermTerm pt2) of
         Left True           -> Left True
         Left False          -> Left False
         Right (pop, t1, t2) -> Right $ PAtom pop pt1' pt2'
                                where (pt1', pt2') = case pt1 of
                                                          PTPtr _ -> (PTPtr t1, PTPtr t2)
                                                          PTInt _ -> (PTInt t1, PTInt t2)

mkPRel :: (?spec::Spec) => String -> [Expr] -> Predicate
mkPRel r as = undefined
