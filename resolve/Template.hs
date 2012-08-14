module Template(Template(port, derive, var, inst, process, method), 
                Port(portTemplate), 
                Derive(drvTemplate), 
                Instance(instTemplate)) where

import Pos
import Name

import qualified Const    as C
import qualified Var      as V
import qualified Process  as P
import qualified Method   as M
import qualified TypeSpec as T

-- Template port
data Port = Port { portPos      :: Pos
                 , portTemplate :: Ident
                 , portName     :: Ident}

instance WithName Port where
    name = portName

instance WithPos Port where
    pos = portPos

-- Derive clause
data Derive = Derive { drvPos      :: Pos
                     , drvTemplate :: Ident
                     , drvPort     :: [Ident]}

instance WithPos Derive where
    pos = drvPos

-- Template instantiation inside another template
data Instance = Instance { instPos      :: Pos
                         , instTemplate :: Ident
                         , instName     :: Ident
                         , instPort     :: [Ident]}

instance WithName Instance where
    name = instName


-- Template
data Template = Template { tpos     :: Pos
                         , tname    :: Ident
                         , port     :: [Port]
                         , derive   :: [Derive]
                         , const    :: [C.Const]
                         , typedecl :: [T.TypeDecl]
                         , var      :: [V.Var]
                         , inst     :: [Instance]
                         , process  :: [P.Process]
                         , method   :: [M.Method]}

instance WithPos Template where
    pos = tpos

instance WithName Template where
    name = tname
