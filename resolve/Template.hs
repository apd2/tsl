module Template(Template(tmPort, tmDerive, tmVar, tmInst, tmProcess, tmMethod), 
                Port(portTemplate), 
                Derive(drvTemplate, drvPort), 
                Instance(instTemplate, instPort)) where

import PP
import Pos
import Name
import Const
import Var
import Process
import Method
import TypeSpec

-- Template port
data Port = Port { ppos         :: Pos
                 , portTemplate :: Ident
                 , pname        :: Ident}

instance PP Port where
    pp p = portTemplate p <+> name p

instance WithName Port where
    name = pname

instance WithPos Port where
    pos = ppos

-- Derive clause
data Derive = Derive { dpos        :: Pos
                     , drvTemplate :: Ident
                     , drvPort     :: [Ident]}

instance PP Derive where
    pp (Derive _ t []) = pp text "derive" <+> pp n
    pp (Derive _ t ps) = text "derive" <+> pp n <+> (parens $ hsep $ punctuate comma $ map pp ps)

instance WithPos Derive where
    pos = dpos

---- Template instantiation inside another template
--data Instance = Instance { ipos         :: Pos
--                         , instTemplate :: Ident
--                         , iname        :: Ident
--                         , instPort     :: [Ident]}
--
--instance WithPos Instance where
--    pos = ipos
--
--instance WithName Instance where
--    name = iname


-- Init block
data Init = Init { inpos    :: Pos
                 , initBody :: Expr}

instance PP Init where
    pp (Init _ b) = text "init" $+$ pp s

instance WithPos Init where
    pos = inpos

-- Goal
data Goal = Goal { gpos     :: Pos
                 , gname    :: Ident
                 , goalCond :: Expr}

instance PP Goal where
    pp (Goal _ n c) = text "goal" <+> pp n <+> char '=' <+> pp c

instance WithPos Goal where
    pos = gpos

instance WithName Goal where
    name = gname

-- Continuous assignment
data ContAssign = ContAssign { apos    :: Pos
                             , cassLHS :: Expr
                             , cassRHS :: Expr}

instance PP ContAssign where
    pp (ContAssign _ l r) = text "assign" <+> pp l <+> char '=' <+> pp r

instance WithPos ContAssign where
    pos = apos

-- Template-global variable
data GVar = GVar { gpos       :: Pos
                 , gvarExport :: Bool
                 , gvarVis    :: Bool
                 , gvar       :: Var}

instance PP GVar where
    pp v =  (if (gvarExport v) then text "export" else empty) 
        <+> (if (gvarVis v) then empty else text "invisible") 
        <+> pp (gvar v)

instance WithPos GVar where
    pos       = gpos
    atPos v p = v{gpos = p}

instance WithName GVar where
    name = name . gvar

instance WithType GVar where
    typ = typ . gvar

-- Template
data Template = Template { tpos       :: Pos
                         , tname      :: Ident
                         , tmPort     :: [Port]
                         , tmDerive   :: [Derive]
                         , tmConst    :: [Const]
                         , tmTypeDecl :: [TypeDecl]
                         , tmVar      :: [GVar]
                         --, tmInst     :: [Instance]
                         , tmInit     :: [Init]
                         , tmProcess  :: [Process]
                         , tmMethod   :: [Method]}

instance PP Template where
    pp t = text "template" <+> (pp $ name t) <+> (ppports $ tmPort t) $+$ 
                               ppitems (tmDerive t)   $+$
                               --ppitems (tmInst t)     $+$
                               ppitems (tmTypeDecl t) $+$
                               ppitems (tmConst t)    $+$
                               ppitems (tmVar t)      $+$
                               ppitems (tmInit t)     $+$
                               ppitems (tmProcess t)  $+$
                               ppitems (tmMethod t)   $+$
           text "endtemplate"
        where ppports [] = text ""
              ppports ports = parens $ hsep $ punctuate comma $ map pp ports
              ppitems = vcat $ map ((<> semi) . ppitem

instance WithPos Template where
    pos = tpos

instance WithName Template where
    name = tname
