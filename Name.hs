-- Identifiers and paths

{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}

module Name(Ident(..), 
            StaticSym, 
            GStaticSym, 
            WithName(..)) where

import Pos

data Ident = Ident Pos String

instance Show Ident where
    show (Ident _ n) = n

instance Eq Ident where
    (==) (Ident _ n1) (Ident _ n2) = (n1 == n2)

instance WithPos Ident where
    pos (Ident p _) = p

type StaticSym = [Ident]
type GStaticSym = StaticSym

class WithName a where
    name :: a -> Ident
