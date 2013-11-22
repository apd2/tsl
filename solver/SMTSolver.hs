-- Generic interface of an SMT solver

module SMTSolver (SMTSolver(..)) where

import Store
import BFormula

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
