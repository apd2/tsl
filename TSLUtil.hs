{-# LANGUAGE FlexibleContexts #-}

module TSLUtil(err,
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

-- Check for duplicate declarations
uniqNames :: (MonadError String me, WithPos a, WithName a) => String -> [a] -> me ()
uniqNames m xs = do 
    foldM (\xs' x -> case find ((== name x) . name) xs' of
                          Nothing -> return $ x:xs'
                          Just y  -> err (pos x) $ "Duplicate " ++ m ++ " " ++ show (name x) ++ " previous declaration: " ++ show (pos y)) 
          [] xs
    return ()


-- Find a cycle in a graph
grCycle :: Graph gr => gr a b -> Maybe [LNode a]
grCycle g = case mapMaybe nodeCycle (nodes g) of
                 []  -> Nothing
                 c:_ -> Just c
  where
    nodeCycle n = listToMaybe $ map (\s -> map (\id -> (id, fromJust $ lab g id)) (n:(esp s n g))) $ 
                                filter (\s -> elem n (reachable s g)) $ suc g n
