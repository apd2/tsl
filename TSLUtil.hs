{-# LANGUAGE FlexibleContexts #-}

module TSLUtil(err,
               assert,
               uniqNames,
               grCycle,
               bitWidth,
               readBin,
               graphUpdNode,
               graphChangeNodeID,
               graphTrace,
               graphTraceFile,
               graphTraceFileMany,
               graphShow,
               graphSave,
               traceFile,
               sanitize) where

import Control.Monad.Error
import Data.List
import Data.Maybe
import Data.Graph.Inductive
import Data.Graph.Inductive.Graphviz 

import System.IO.Unsafe
import Data.IORef
import Data.Bits
import System.IO.Unsafe
import System.Process
import Data.String.Utils

import Util hiding (name)
import Pos
import Name

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


-- The number of bits required to encode range [0..i]
bitWidth :: (Integral a) => a -> Int
bitWidth i = 1 + log2 (fromIntegral i)

-- parse binary number
readBin :: String -> Integer
readBin s = foldl' (\acc c -> (acc `shiftL` 1) +
                              case c of
                                   '0' -> 0
                                   '1' -> 1) 0 s

-- Graph operations --

graphUpdNode :: Node -> (a -> a) -> Gr a b -> Gr a b
graphUpdNode n f g = (pre, n', f x, suc) & g' 
    where (Just (pre, n', x, suc), g') = match n g 
    
graphChangeNodeID :: Node -> Node -> Gr a b -> Gr a b
graphChangeNodeID n n' g = (pre', n', x, suc') & g' 
    where (Just (pre, _, x, suc), g') = match n g 
          pre' = map (\(l,m) -> if' (m==n) (l,n') (l,m)) pre
          suc' = map (\(l,m) -> if' (m==n) (l,n') (l,m)) suc
    
-- Graph visualisation --

sanitize :: String -> String
sanitize title = replace "("  "" 
               $ replace ")"  "" 
               $ replace "'"  "" 
               $ replace "\"" "_" 
               $ replace "/"  "_" 
               $ replace "$"  "" 
               $ replace ":"  "_" 
               $ replace "="  "_"
               $ replace "<"  "_"
               $ replace ">"  "_"
               $ replace "+"  "_"
               $ replace " "  "_"
               $ replace "."  "_"
               $ replace "["  "_"
               $ replace "]"  "_"
               $ replace "&"  "_"
               $ replace "#"  "_"
               $ replace "?"  "_"
               $ replace ","  "_"
               $ replace "%"  "_"
               title

graphTrace :: (Show b, Show c) => Gr b c -> String -> a -> a
graphTrace g title x = unsafePerformIO $ do
    graphShow g title
    return x

graphTraceFile :: (Show b, Show c) => Gr b c -> String -> a -> a
graphTraceFile g title x = unsafePerformIO $ do
    _ <- graphSave g title False
    return x

graphTraceFileMany :: (Show b, Show c) => [Gr b c] -> String -> a -> a
graphTraceFileMany gs title x = unsafePerformIO $ do
    fnames <- mapM (\(g,n) -> graphSave g (title++show n) True) $ zip gs ([1..]::[Int])
    _ <- readProcess "pdftk" (fnames ++ ["cat", "output", (sanitize title) ++ ".pdf"]) ""
    return x

graphShow :: (Show b, Show c) => Gr b c -> String -> IO ()
graphShow g title = do
    fname <- graphSave g title True
    _ <- readProcess "evince" [fname] ""
    return ()

graphSave :: (Show b, Show c) => Gr b c -> String -> Bool -> IO String
graphSave g title tmp = do
    let -- Convert graph to dot format
        title' = sanitize title
        fname = (if tmp then "/tmp/" else "") ++ title' ++ ".pdf"
        graphstr = graphToDot g title'
    writeFile (fname++".dot") graphstr
    _ <- readProcess "dot" ["-Tpdf", "-o" ++ fname] graphstr 
    return fname

graphToDot :: (Show b, Show c) => Gr b c -> String -> String
graphToDot g title = graphviz g' title (6.0, 11.0) (1,1) Portrait
    where g' = emap (eformat . show)
               $ gmap (\(inb, n, l, outb) -> (inb, n, show n ++ ": " ++ (nformat $ show l), outb)) g
          maxLabel = 64
          nformat :: String -> String
          nformat s = if' (length s <= maxLabel) s ((take maxLabel s) ++ "...") 
          eformat :: String -> String
          eformat s | length s <= maxLabel = s
                    | otherwise            = (take maxLabel s) ++ "\n" ++ eformat (drop maxLabel s)

traceFile :: String -> FilePath -> a -> a
traceFile str fname x = unsafePerformIO $ do
    writeFile (sanitize fname) str
    return x
