module Frontend.Transducer() where

data Transducer = Transducer { txpos            :: Pos
                             , txOutType        :: TypeSpec
                             , txName           :: Ident
                             , txInput          :: [TxInput]
                             , txBody           :: Either TxComposite Statement}


