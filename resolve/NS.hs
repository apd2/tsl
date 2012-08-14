-- Namespace type class

{-# LANGUAGE MultiParamTypeClasses #-}

module NS(NS(..)) where

import Prelude hiding (lookup)
import Data.List hiding (lookup)

import Name
import Pos

class NS a b where
    lookup :: a -> Ident -> Maybe b
    rlookup :: a -> [Ident] -> Maybe b
    (!) :: a -> Ident -> b
    (!) x i = case lookup x i of
                   Nothing -> error $ "NS.lookup failed: " ++ show i
                   Just y -> y
    (!!) :: a -> [Ident] -> b
    (!!) x is = case rlookup x is of
                     Nothing -> error $ "NS.rlookup failed " ++ (intercalate "." $ map show is)
                     Just y -> y
