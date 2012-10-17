module Cascade(Cascade(..),
               casMap,
               FCascade,
               ECascade,
               BCascade,
               TCascade,
               fcasToFormula,
               fcasPrune) where

import Data.Functor
import Control.Applicative
import Data.List

import TSLUtil
import ISpec
import IExpr
import Formula
import Predicate

-- Intermediate data structure that represents the value of
-- an arithmetic expression depending on pointer predicates
-- or other conditions
data Cascade a = CasTree  [(Formula, Cascade a)] 
               | CasLeaf a

ctrue :: Cascade Expr
ctrue = CasLeaf true

-- Map leaves of a cascade to cascades
casMap :: (a -> Cascade b) -> Cascade a -> Cascade b
casMap f (CasLeaf x)  = f x
casMap f (CasTree bs) = CasTree $ map (mapSnd (casMap f)) bs

instance Functor Cascade where
    fmap f (CasLeaf l)  = CasLeaf $ f l
    fmap f (CasTree bs) = CasTree $ map (mapSnd (fmap f)) bs

-- TODO: prune inconsistent branches
instance Applicative Cascade where
    pure  x    = CasLeaf x
    (<*>) cf c = casMap (\f -> fmap f c) cf

type FCascade = Cascade Formula
type BCascade = Cascade Bool
type ECascade = Cascade Expr
type TCascade = Cascade Term

fcasToFormula :: FCascade -> Formula
fcasToFormula (CasLeaf f)      = f
fcasToFormula (CasTree [])     = FFalse
fcasToFormula (CasTree (b:bs)) = foldl' (\f (c,cas) -> fdisj [f, fconj [c, fcasToFormula cas]]) 
                                        (fconj [fst b, fcasToFormula $ snd b]) bs

-- Recursively prune false leaves
fcasPrune :: FCascade -> FCascade
fcasPrune (CasLeaf f)  = CasLeaf f
fcasPrune (CasTree bs) = if null bs' then CasLeaf FFalse else CasTree bs'
    where bs' = filter (\(f,cas) -> case cas of 
                                         CasLeaf FFalse -> False
                                         _              -> True)
                       $ map (mapSnd fcasPrune) bs
