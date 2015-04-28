module Abstract.BDDHelpers(disj,
                  conj,
                  eqConst,
                  eqVars,
                  bimp) where

import Control.Monad.ST
import Control.Monad
import Data.Bits

import Util
import Cudd.Imperative


disj :: DDManager s u -> [DDNode s u] -> ST s (DDNode s u)
disj m [] = return $ bZero m
disj m (x:xs) = do
    ref x
    foldM (\acc x -> do res <- bOr m acc x
                        deref m acc
                        return res) x xs

conj :: DDManager s u -> [DDNode s u] -> ST s (DDNode s u)
conj m [] = return $ bOne m
conj m (x:xs) = do
    ref x
    foldM (\acc x -> do res <- bAnd m acc x
                        deref m acc
                        return res) x xs

eqConst :: (Bits b) => DDManager s u -> [DDNode s u] -> b -> ST s (DDNode s u)
eqConst m v x = computeCube m v (bitsToBoolArrBe (length v) x)

eqVars :: DDManager s u -> [DDNode s u] -> [DDNode s u] -> ST s (DDNode s u)
eqVars m v1 v2 = do
    bits <- zipWithM (bXnor m) v1 v2
    res  <- conj m bits
    mapM (deref m) bits
    return res

bimp :: DDManager s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
bimp m x y = bOr m (bNot x) y
