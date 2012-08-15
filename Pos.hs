module Pos(Pos, WithPos(..)) where

import Text.Parsec.Pos

type Pos = (SourcePos,SourcePos)

class WithPos a where
    pos   :: a -> Pos
    atPos :: a -> Pos -> a

