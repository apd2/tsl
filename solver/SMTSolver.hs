-- Generic interface of an SMT solver

module SMTSolver (SMTSolver(..),
                  smtCheckSAT) where

import Store
import BFormula

data SMTSolver = SMTSolver {
    -- Input:  list of formula
    -- Output: Nothing    - satisfiability of the formula could not be established
    --         Just Left  - unsat core of the conjunction of formula
    --         Just Right - satisfying assignment (unassigned variables are don't cares)
    smtGetModel :: [Formula] -> Maybe (Either [Int] Store)
}

smtCheckSAT :: SMTSolver -> [Formula] -> Maybe Bool
smtCheckSAT solver fs = case smtGetModel solver fs of
                             Just (Right _) -> Just True
                             Just (Left _)  -> Just False
                             Nothing        -> Nothing
