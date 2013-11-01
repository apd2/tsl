{-# LANGUAGE RecordWildCards #-}

module Relation (RArg(RArg),
                 Relation(Relation, relName, relArg, relRule),
                 Apply(Apply, applyRel, applyArg)) where

import Text.PrettyPrint

import Pos
import Name
import Expr
import PP
import Type

data RArg = RArg { apos  :: Pos
                 , atype :: TypeSpec
                 , aname :: Ident}

instance PP RArg where
    pp RArg{..} = pp atype <+> pp aname

instance Show RArg where
    show = render . pp

instance WithName RArg where
    name = aname

instance WithPos RArg where
    pos       = apos
    atPos a p = a{apos = p}

instance WithTypeSpec RArg where 
    tspec = atype

data Relation = Relation { rpos    :: Pos
                         , relName :: Ident
                         , relArg  :: [RArg]
                         , relRule :: [Expr]
                         }

instance PP Relation where
    pp Relation{..} = text "relation" <+> pp relName <+> (parens $ hsep $ punctuate comma $ map pp relArg) $+$
                      (vcat $ map ((text "|==" <+>) . pp) relRule) 

instance WithName Relation where
    name = relName

instance WithPos Relation where
    pos       = rpos
    atPos a p = a{rpos = p}

data Apply = Apply { appos    :: Pos
                   , applyRel :: Ident
                   , applyArg :: [Expr]
                   }

instance PP Apply where
    pp Apply{..} = text "rule" <+> pp applyRel <+> (parens $ hsep $ punctuate comma $ map pp applyArg)

instance WithPos Apply where
    pos       = appos
    atPos a p = a{appos = p}
