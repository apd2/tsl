module Template(Template(tmPort, tmDerive, tmVar, tmInst, tmProcess, tmMethod), 
                Port(portTemplate), 
                Derive(drvTemplate, drvPort), 
                Instance(instTemplate, instPort)) where

import Pos
import Name

import Const
import Var
import Process
import Method
import TypeSpec

-- Template port
data Port = Port { ppos         :: Pos
                 , pname        :: Ident                 
                 , portTemplate :: Ident
                 }

instance WithName Port where
    name = pname

instance WithPos Port where
    pos = ppos

-- Derive clause
data Derive = Derive { dpos        :: Pos
                     , drvTemplate :: Ident
                     , drvPort     :: [Ident]}

instance WithPos Derive where
    pos = dpos

-- Template instantiation inside another template
data Instance = Instance { ipos         :: Pos
                         , instTemplate :: Ident
                         , iname        :: Ident
                         , instPort     :: [Ident]}

instance WithPos Instance where
    pos = ipos

instance WithName Instance where
    name = iname


-- Template
data Template = Template { tpos       :: Pos
                         , tname      :: Ident
                         , tmPort     :: [Port]
                         , tmDerive   :: [Derive]
                         , tmConst    :: [Const]
                         , tmTypeDecl :: [TypeDecl]
                         , tmVar      :: [Var]
                         , tmInst     :: [Instance]
                         , tmProcess  :: [Process]
                         , tmMethod   :: [Method]}

instance WithPos Template where
    pos = tpos

instance WithName Template where
    name = tname
