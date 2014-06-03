-- Generic interface of an SMT solver

module Solver.SMTSolver (SMTSolver(..)) where

import Solver.Store
import Abstract.BFormulaTypes

data SMTSolver = SMTSolver {
    -- Input:  list of formula
    -- Output: Nothing    - satisfiability of the formula could not be established
    --         Just Left  - unsat core of the conjunction of formula
    --         Just Right - satisfying assignment (unassigned variables are don't cares)
    smtGetModel       :: [Formula] -> Maybe (Maybe Store),
    smtCheckSAT       :: [Formula] -> Maybe Bool,
    smtGetCore        :: [Formula] -> Maybe (Maybe [Int]),
    smtGetModelOrCore :: [Formula] -> Maybe (Either [Int] Store)
}
