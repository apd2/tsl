{-# LANGUAGE RecordWildCards, ImplicitParams, TupleSections #-}

module Internal.ITransducer(TxInstance(..),
                            Transducer(..),
                            TxPortRef(..)) where

import Internal.CFA
import Internal.IType
import Internal.IVar

data TxPortRef = TxInputRef String
               | TxLocalRef String String
               deriving (Eq)

data TxInstance = TxInstance { tiTxName   :: String
                             , tiInstName :: String
                             , tiInputs   :: [TxPortRef]
                             }

data Transducer = Transducer { txName           :: String
                             , txInput          :: [(Type, String)]
                             , txOutput         :: [(Type, String)]
                             , txBody           :: Either ([TxPortRef], [TxInstance]) (CFA, [Var])
                             }
