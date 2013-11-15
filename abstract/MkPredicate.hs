{-# LANGUAGE ImplicitParams #-}

module MkPredicate (mkAtom) where

import Predicate
import BVSMT
import ISpec

-- All atoms must be created by this function
mkAtom :: (?spec::Spec) => RelOp -> PTerm -> PTerm -> Either Bool Predicate
mkAtom op pt1 pt2 = 
    case bvRelNormalise op (ptermTerm pt1) (ptermTerm pt2) of
         Left True           -> Left True
         Left False          -> Left False
         Right (pop, t1, t2) -> Right $ PAtom pop pt1' pt2'
                                where (pt1', pt2') = case pt1 of
                                                          PTPtr _ -> (PTPtr t1, PTPtr t2)
                                                          PTInt _ -> (PTInt t1, PTInt t2)
