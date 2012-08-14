-- Identifiers and paths

{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}

module Name(Ident,Selector,Path,GlobalPath, WithName(..)) where

import Pos
import qualified Expr as E

data Ident = Ident Pos String

instance WithPos Ident where
    pos (Ident p _) = p



type ScopedIdent = [Ident]

data Selector = Field Ident
              | Index Pos E.Expr


instance WithPos Selector where
    pos (Field i)  = pos i
    pos (Index p _)  = p

data Path = Path ScopedIdent [Selector]

instance WithPos Path where
    pos path = (fst $ pos $ head path, 
                snd $ pos $ last path)

type GlobalPath = Path


class WithName a where
    name :: a -> Ident
