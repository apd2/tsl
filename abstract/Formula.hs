module Formula(BoolBOp(..),
               Formula(..),
               fdisj,
               fconj,
               bopToBoolOp,
               boolOpToBOp) where

import Data.List

import Predicate
import Common

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

boolOpToBOp :: BoolBOp -> BOp
boolOpToBOp Conj  = And
boolOpToBOp Disj  = Or
boolOpToBOp Impl  = Imp
boolOpToBOp Equiv = Eq

-- Formula consists of predicates and boolean constants
-- connected with boolean connectors
data Formula = FTrue
             | FFalse
             | FPred    Predicate
             | FBinOp   BoolBOp Formula Formula
             | FNot     Formula
             deriving (Eq)

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

