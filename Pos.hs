module Pos(Pos, 
           WithPos(..),
           spos,
           nopos) where

import Text.Parsec.Pos

type Pos = (SourcePos,SourcePos)

class WithPos a where
    pos   :: a -> Pos
    atPos :: a -> Pos -> a

spos :: (WithPos a) => a -> String
spos x = show $ pos x

nopos::Pos 
nopos = (initialPos "",initialPos "")
