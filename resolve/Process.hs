module Process(Process) where

import Pos
import Name
import qualified Var as V

data Process = Process { ppos  :: Pos
                       , pname :: Ident
                       , var   :: [V.Var]}

instance WithPos Process where
    pos = ppos

instance WithName Process where
    name = pname
