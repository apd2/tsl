module Main where

import qualified Data.Map as M
import Control.Monad
import Data.Maybe
import System.Environment
import Text.Parsec
import qualified Text.PrettyPrint as P

import Syntax
import Parse

main = do
    args <- getArgs
    f <- case args of
             [] -> fail $ "File name required"
             _ -> return $ head args
    parseTSL M.empty f
    putStrLn "ok"

-- Recursively parse TSL file and all of its imports
-- Takes a map of already parsed files and the name of the file
-- to parse
parseTSL :: M.Map FilePath Spec -> FilePath -> IO (M.Map FilePath Spec)
parseTSL modules f = do
    tsl <- readFile f
    --putStr tsl
    spec <- case parse grammar f tsl of
                 Left e -> fail $ show e
                 Right st -> return st
    writeFile (f ++ ".out") $ P.render $ pp spec
    -- Parse imports
    foldM (\mods imp -> if M.member imp mods
                           then return mods
                           else parseTSL mods imp)
          (M.insert f spec modules) (imports spec)

-- Extract the list of imports from parsed TSL spec
imports :: Spec -> [FilePath]
imports s = mapMaybe (\item -> case getVal item of
                                    SpImport (Import name) -> Just $ getVal name
                                    _ -> Nothing) s
