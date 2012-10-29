{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Pos(Pos, 
           WithPos(..),
           spos,
           nopos) where

import Text.Parsec.Pos

type Pos = (SourcePos,SourcePos)

class WithPos a where
    pos   :: a -> Pos
    atPos :: a -> Pos -> a

instance WithPos Pos where
    pos   = id
    atPos = error "Not implemented: atPos Pos"   

spos :: (WithPos a) => a -> String
spos x = let p = fst $ pos x
         in sourceName p ++ ":" ++ (show $ sourceLine p) ++ ":" ++ (show $ sourceColumn p)

nopos::Pos 
nopos = (initialPos "",initialPos "")
