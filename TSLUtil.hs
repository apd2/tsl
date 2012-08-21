{-# LANGUAGE FlexibleContexts #-}

module TSLUtil(err,
               assert,
               uniqNames,
               grCycle) where

import Control.Monad.Error
import Data.List
import Data.Maybe
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.BFS
import Data.Graph.Inductive.Query.DFS

import Pos
import Name

err :: (MonadError String me) => Pos -> String -> me a
err p e = throwError $ show p ++ ": " ++ e

assert :: (MonadError String me) => Bool -> Pos -> String -> me a
assert b p m = 
    if b 
       then return ()
       else err p m

-- Check for duplicate declarations
uniqNames :: (MonadError String me, WithPos a, WithName a) => (String -> String) -> [a] -> me ()
uniqNames msgfunc xs = do
    case filter ((>1) . length) $ groupBy (\x1 x2 -> name x1 == name x2) xs of
         []        -> return ()
         g@(x:_):_ -> err (pos x) $ msgfunc (sname x) ++ " at the following locations:\n  " ++ (intercalate "\n  " $ map spos g)

-- Find a cycle in a graph
grCycle :: Graph gr => gr a b -> Maybe [LNode a]
grCycle g = case mapMaybe nodeCycle (nodes g) of
                 []  -> Nothing
                 c:_ -> Just c
  where
    nodeCycle n = listToMaybe $ map (\s -> map (\id -> (id, fromJust $ lab g id)) (n:(esp s n g))) $ 
                                filter (\s -> elem n (reachable s g)) $ suc g n
