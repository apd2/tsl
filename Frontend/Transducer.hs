{-# LANGUAGE RecordWildCards #-}

module Frontend.Transducer(Transducer(Transducer, txOutType, txInput, txBody),
                           TxInput(TxInput, txiType, txiName),
                           TxInstance(TxInstance, tiTxName, tiInstName, tiInputs)) where

import Text.PrettyPrint

import PP
import Pos
import Name
import Frontend.Statement
import Frontend.Type


data TxInput = TxInput { txipos         :: Pos
                       , txiType        :: TypeSpec
                       , txiName        :: Ident
                       }

instance PP TxInput where
    pp TxInput{..} = pp txiType <+> pp txiName
    
instance Show TxInput where
    show      = render . pp

instance WithName TxInput where
    name = txiName

instance WithPos TxInput where
    pos       = txipos
    atPos i p = i{txipos = p}

instance WithTypeSpec TxInput where 
    tspec = txiType

data TxInstance = TxInstance { tipos      :: Pos
                             , tiTxName   :: Ident
                             , tiInstName :: Ident
                             , tiInputs   :: [Ident]
                             }

instance PP TxInstance where
    pp TxInstance{..} = text "instance" <+> pp tiTxName <+> pp tiInstName 
                             <> (parens $ hsep $ punctuate comma $ map pp tiInputs)
    
instance Show TxInstance where
    show      = render . pp

instance WithName TxInstance where
    name = tiInstName

instance WithPos TxInstance where
    pos       = tipos
    atPos i p = i{tipos = p}

data Transducer = Transducer { txpos            :: Pos
                             , txOutType        :: TypeSpec
                             , txName           :: Ident
                             , txInput          :: [TxInput]
                             , txBody           :: Either [TxInstance] Statement
                             }

instance PP Transducer where
    pp Transducer{..} = text "transducer" <+> pp txOutType <+> pp txName 
                     $$ case txBody of
                             Left is -> lbrace $$ (nest' $ vcat $ map pp is) $$ rbrace
                             Right s -> pp s

instance Show Transducer where
    show      = render . pp

instance WithName Transducer where
    name = txName

instance WithPos Transducer where
    pos       = txpos
    atPos t p = t{txpos = p}
