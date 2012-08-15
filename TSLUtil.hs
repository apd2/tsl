{-# LANGUAGE FlexibleContexts #-}

module TSLUtil(err) where

import Control.Monad.Error

import Pos

err :: (MonadError String me) => Pos -> String -> me a
err p e = throwError $ show p ++ ": " ++ e
