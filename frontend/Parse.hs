{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, RecordWildCards, UndecidableInstances, TupleSections #-}

module Parse (parseTSL) where

import qualified Data.Map         as M
import Text.Parsec
import qualified Text.PrettyPrint as P
import Data.List
import Data.Maybe
import Control.Monad
import System.Directory


import Grammar
import PP
import Name

-- Recursively parse TSL file and all of its imports
-- Takes a map of already parsed files and the name of the file
-- to parse
parseTSL :: M.Map FilePath [SpecItem] -> FilePath -> [FilePath] -> IO (M.Map FilePath [SpecItem])
parseTSL modules f dirs = do
    tsl <- readFile f
    --putStr tsl
    spec <- case parse grammar f tsl of
                 Left e -> fail $ show e
                 Right st -> return st
    writeFile (f ++ ".out") $ concatMap (P.render . pp) spec
    -- Parse imports
    foldM (\mods imp -> do imp' <- findImport imp dirs
                           if M.member imp' mods
                              then return mods
                              else parseTSL mods imp' dirs)
          (M.insert f spec modules) (imports spec)

findImport :: FilePath -> [FilePath] -> IO String
findImport f dirs = do
    let dirs' = "":(map (++"/") dirs)
    match <- filterM (\d -> doesFileExist (d ++ f)) dirs'
    case match of
         [] -> fail $ "File not found: " ++ f
         _  -> return $ head match ++ f

-- Extract the list of imports from parsed TSL spec
imports :: [SpecItem] -> [FilePath]
imports s = mapMaybe (\item -> case item of
                                    SpImport (Import _ (Ident _ n)) -> Just n
                                    _                               -> Nothing) s

