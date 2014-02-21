{-# LANGUAGE ImplicitParams #-}

module BVSMT where

bvRelNormalise :: (?spec::Spec) => RelOp -> Term -> Term -> Either Bool (Bool, PredOp, Term, Term)
bvTermNormalise :: (?spec::Spec) => Term -> Term
bvSolver :: Spec -> SMTSolver -> C.STDdManager s u  -> TheorySolver s u AbsVar AbsVar Var
