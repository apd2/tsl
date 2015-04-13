{-# LANGUAGE RecordWildCards, ImplicitParams, TupleSections #-}

module Internal.ITransducer(TxInstance(..),
                            Transducer(..)) where

import Internal.CFA
import Internal.IType
import Internal.IVar

data TxInstance = TxInstance { tiTxName   :: String
                             , tiInstName :: String
                             , tiInputs   :: [String]
                             }

data Transducer = Transducer { txOutType        :: Type
                             , txName           :: String
                             , txInput          :: [(Type, String)]
                             , txBody           :: Either [TxInstance] (CFA, [Var])
                             }


