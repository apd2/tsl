module Process(Process(Process,procStatement),
               procVar) where

import Text.PrettyPrint

import Pos
import Name
import PP
import Var
import Statement

data Process = Process { ppos          :: Pos
                       , pname         :: Ident
                       , procStatement :: Statement}

procVar :: Process -> [Var]
procVar p = stmtVar $ procStatement p

instance PP Process where
    pp p = (text "process" <+> (pp $ name p)) $+$ (pp $ procStatement p)

instance WithPos Process where
    pos        = ppos
    atPos pr p = pr{ppos = p}

instance WithName Process where
    name = pname
