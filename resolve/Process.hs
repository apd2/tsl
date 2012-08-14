module Process(Process(procVar)) where

import Pos
import Name
import Var

data Process = Process { ppos    :: Pos
                       , pname   :: Ident
                       , procVar :: [Var]}

instance WithPos Process where
    pos = ppos

instance WithName Process where
    name = pname
