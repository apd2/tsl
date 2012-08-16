{-# LANGUAGE FlexibleContexts #-}

module TSLUtil(err,
               uniqNames) where

import Control.Monad.Error

import Pos
import Name

err :: (MonadError String me) => Pos -> String -> me a
err p e = throwError $ show p ++ ": " ++ e

uniqNames :: (MonadError String me, WithPos a, WithName a) => String -> [a] -> me ()
uniqNames m xs = do 
    foldM (\xs' x -> case find ((== name x) . name) xs' of
                          Nothing -> x:xs'
                          Just y  -> err (pos x) $ "Duplicate " ++ m ++ " " ++ show (name x) ++ " previous declaration: " ++ show (pos y)) 
          [] xs
    return ()
