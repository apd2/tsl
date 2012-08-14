module Template(Template) where

import Pos
import Name

import qualified Const    as C
import qualified Var      as V
import qualified Process  as P
import qualified Method   as M
import qualified TypeSpec as T
import Obj


-- Template port
data Port = Port { portPos      :: Pos
                 , portTemplate :: Ident
                 , portName     :: Ident}

instance WithName Port where
    name = portName

instance WithPos Port where
    pos = portPos

instance (?spec::S.Spec) => NS Port Obj where
    lookup p = lookup (S.getTemplate ?spec (portTemplate p))


-- Derive clause
data Derive = Derive { drvPos      :: Pos
                     , drvTemplate :: Ident
                     , drvPort     :: [Path]}

instance WithPos Derive where
    pos = drvPos

instance (?spec::S.Spec) => NS Derive Obj where
    lookup d = lookup (S.getTemplate ?spec (drvTemplate d))

-- Template instantiation inside another template
data Instance = Instance { instPos      :: Pos
                         , instTemplate :: Ident
                         , instName     :: Ident
                         , instPort     :: [Path]}

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

instance (?spec::S.Spec) => NS Template Obj where
    lookup t (Field n) = listToMaybe [p,c,v,i,pr,m,par]
        where -- search for the name in the local scope
              p  = fmap ObjPort     $ find ((== n) . name) (port t)
              v  = fmap ObjVar      $ find ((== n) . name) (var t)
              i  = fmap ObjInstance $ find ((== n) . name) (inst t)
              pr = fmap ObjProcess  $ find ((== n) . name) (process t)
              m  = fmap ObjMethod   $ find ((== n) . name) (method t) 
              -- search parent templates
              par = listToMaybe $ map (d -> lookup d (Field n)) (derive t)

    lookup t _ = Nothing

instance StaticNS Template Obj where
    slookup t i = listToMaybe [c,e]
        where -- search for the name in the local scope
              c = fmap ObjConst $ find ((== n) . name) (const t)
              e = listToMaybe $ map (\t -> slookup t i) (typedecl t)
