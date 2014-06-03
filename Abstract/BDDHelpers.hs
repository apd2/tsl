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


disj :: STDdManager s u -> [DDNode s u] -> ST s (DDNode s u)
disj m [] = return $ bzero m
disj m (x:xs) = do
    ref x
    foldM (\acc x -> do res <- bor m acc x
                        deref m acc
                        return res) x xs

conj :: STDdManager s u -> [DDNode s u] -> ST s (DDNode s u)
conj m [] = return $ bone m
conj m (x:xs) = do
    ref x
    foldM (\acc x -> do res <- band m acc x
                        deref m acc
                        return res) x xs

eqConst :: (Bits b) => STDdManager s u -> [DDNode s u] -> b -> ST s (DDNode s u)
eqConst m v x = computeCube m v (bitsToBoolArrBe (length v) x)

eqVars :: STDdManager s u -> [DDNode s u] -> [DDNode s u] -> ST s (DDNode s u)
eqVars m v1 v2 = do
    bits <- zipWithM (bxnor m) v1 v2
    res  <- conj m bits
    mapM (deref m) bits
    return res

bimp :: STDdManager s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)
bimp m x y = bor m (bnot x) y
