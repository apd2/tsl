-- Identifiers and paths

{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}

module Name(Ident(..), 
            StaticSym, 
            GStaticSym, 
            WithName(..),
            sname) where

import Text.PrettyPrint

import PP
import Pos

data Ident = Ident Pos String

instance Show Ident where
    show (Ident _ n) = n

instance PP Ident where
    pp (Ident _ n) = text n

instance Eq Ident where
    (==) (Ident _ n1) (Ident _ n2) = (n1 == n2)

instance Ord Ident where
    compare (Ident _ i1) (Ident _ i2) = compare i1 i2

instance WithPos Ident where
    pos (Ident p _)     = p
    atPos (Ident _ n) p = Ident p n

type StaticSym = [Ident]

instance PP StaticSym where
    pp s = hcat $ punctuate (text "::") (map pp s)

instance WithPos StaticSym where
    pos s = ((fst $ pos $ head s),(snd $ pos $ last s))
    atPos = error $ "Not implemented: atPos StaticSym"

type GStaticSym = StaticSym

class WithName a where
    name :: a -> Ident

sname :: (WithName a) => a -> String
sname x = show $ name x
