{-# LANGUAGE FlexibleContexts #-}

module TSLUtil(mapFst,
               mapSnd,
               fst3,
               snd3,
               trd3,
               fromLeft,
               fromRight,
               err,
               assert,
               uniqNames,
               grCycle,
               Uniq, 
               newUniq, 
               getUniq,
               bitWidth) where

import Control.Monad.Error
import Data.List
import Data.Maybe
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.BFS
import Data.Graph.Inductive.Query.DFS
import System.IO.Unsafe
import Data.IORef

import Util hiding (name)
import Pos
import Name

mapFst :: (a->b) -> (a,c) -> (b,c)
mapFst f (x,y) = (f x,y)

mapSnd :: (c->b) -> (a,c) -> (a,b)
mapSnd f (x,y) = (x,f y)

fromLeft :: (Either a b) -> a
fromLeft (Left x) = x

fromRight :: (Either a b) -> b
fromRight (Right x) = x

fst3 (x,y,z) = x
snd3 (x,y,z) = y
trd3 (x,y,z) = z

err :: (MonadError String me) => Pos -> String -> me a
err p e = throwError $ spos p ++ ": " ++ e

assert :: (MonadError String me) => Bool -> Pos -> String -> me ()
assert b p m = 
    if b 
       then return ()
       else err p m

-- Check for duplicate declarations
uniqNames :: (MonadError String me, WithPos a, WithName a) => (String -> String) -> [a] -> me ()
uniqNames msgfunc xs = do
    case filter ((>1) . length) $ groupBy (\x1 x2 -> name x1 == name x2) $ 
                                  sortBy (\x1 x2 -> compare (name x1) (name x2)) xs of
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


-- Unique number generator
type Uniq = IORef Integer

-- Create a new generator initialised to 0
newUniq :: Uniq
newUniq = unsafePerformIO $ newIORef 0

getUniq :: Uniq -> Integer
getUniq u = unsafePerformIO $
            do v <- readIORef u
               writeIORef u (v+1)
               return (v+1)

-- The number of bits required to encode range [0..i]
bitWidth :: (Integral a) => a -> Int
bitWidth i = log2 (fromIntegral $ i+1)
