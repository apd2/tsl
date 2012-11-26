module BFormula(BoolBOp(..),
                Formula(..),
                fdisj,
                fconj,
                fnot,
                fAtom,
                bopToBoolOp,
                boolOpToBOp) where

import Data.List
import Text.PrettyPrint

import Predicate
import Common
import PP

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
             | FPred    Predicate
             | FBinOp   BoolBOp Formula Formula
             | FNot     Formula
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

fAtom :: RelOp -> Term -> Term -> Formula
fAtom REq l r | l < r     = FPred $ PAtom REq l r
              | otherwise = FPred $ PAtom REq r l
fAtom RNeq l r = FNot $ fAtom REq l r

