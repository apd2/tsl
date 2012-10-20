module Template(Template(Template, tmPort, tmDerive, tmInst, tmVar, tmProcess, tmMethod, tmTypeDecl, tmConst, tmGoal, tmWire, tmInit), 
                Port(Port,portTemplate), 
                Instance(Instance, instPort, instTemplate),
                GVar(GVar,gvarExport, gvarVar),
                Goal(Goal, goalCond, goalName),
                Init(Init,initBody),
                Wire(Wire,wireExport,wireRHS,wireType,wireName),
                Derive(Derive,drvTemplate)) where

import Text.PrettyPrint
import Data.Maybe

import PP
import Pos
import Name
import Const
import Var
import Process
import Method
import Type
import Expr

-- Template port
data Port = Port { ppos         :: Pos
                 , portTemplate :: Ident
                 , pname        :: Ident}

instance PP Port where
    pp p = (pp $ portTemplate p) <+> (pp $ name p)

instance WithName Port where
    name = pname

instance WithPos Port where
    pos        = ppos
    atPos pr p = pr{ppos = p}

-- Derive clause
data Derive = Derive { dpos        :: Pos
                     , drvTemplate :: Ident}

instance PP Derive where
    pp (Derive _ t) = text "derive" <+> pp t

instance WithPos Derive where
    pos       = dpos
    atPos d p = d{dpos = p}

-- Template instantiation inside another template
data Instance = Instance { ipos         :: Pos
                         , instTemplate :: Ident
                         , iname        :: Ident
                         , instPort     :: [Ident]}

instance PP Instance where
    pp (Instance _ t n p) = text "instance" <+> pp t <+> pp n <+> 
                            case p of
                                 [] -> empty
                                 _  -> parens $ hsep $ punctuate comma $ map pp p

instance WithPos Instance where
    pos       = ipos
    atPos i p = i{ipos = p}

instance WithName Instance where
    name = iname


-- Init block
data Init = Init { inpos    :: Pos
                 , initBody :: Expr}

instance PP Init where
    pp (Init _ b) = text "init" $+$ pp b

instance WithPos Init where
    pos       = inpos
    atPos i p = i{inpos = p}

-- Goal
data Goal = Goal { gpos     :: Pos
                 , goalName :: Ident
                 , goalCond :: Expr}

instance PP Goal where
    pp (Goal _ n c) = text "goal" <+> pp n <+> char '=' <+> pp c

instance WithPos Goal where
    pos       = gpos
    atPos g p = g{gpos = p}

instance WithName Goal where
    name = goalName

-- Wire (variable with continuous assignment)
data Wire = Wire { wpos       :: Pos
                 , wireExport :: Bool
                 , wireType   :: TypeSpec
                 , wireName   :: Ident
                 , wireRHS    :: Maybe Expr}

instance PP Wire where
    pp (Wire _ e t n r) =  (if e then text "export" else empty)
                       <+> text "wire" <+> pp t <+> pp n 
                       <+> (if (isJust r) then char '=' <+> pp r else empty)

instance WithPos Wire where
    pos       = wpos
    atPos w p = w{wpos = p}

instance WithName Wire where
    name      = wireName

instance WithTypeSpec Wire where
    tspec     = wireType

-- Template-global variable
data GVar = GVar { gvpos      :: Pos
                 , gvarExport :: Bool
                 , gvarVar    :: Var}

instance PP GVar where
    pp v =  (if (gvarExport v) then text "export" else empty) 
        -- <+> (if (gvarVis v) then empty else text "invisible") 
        <+> pp (gvarVar v)

instance WithPos GVar where
    pos       = gvpos
    atPos v p = v{gvpos = p}

instance WithName GVar where
    name = name . gvarVar

instance WithTypeSpec GVar where
    tspec = tspec . gvarVar

-- Template
data Template = Template { tpos       :: Pos
                         , tname      :: Ident
                         , tmPort     :: [Port]
                         , tmDerive   :: [Derive]
                         , tmConst    :: [Const]
                         , tmTypeDecl :: [TypeDecl]
                         , tmVar      :: [GVar]
                         , tmWire     :: [Wire]
                         , tmInst     :: [Instance]
                         , tmInit     :: [Init]
                         , tmProcess  :: [Process]
                         , tmMethod   :: [Method]
                         , tmGoal     :: [Goal]}

instance PP Template where
    pp t = text "template" <+> (pp $ name t) <+> (ppports $ tmPort t) $+$ 
                               ppitems (tmDerive t)   $+$
                               ppitems (tmInst t)     $+$
                               ppitems (tmTypeDecl t) $+$
                               ppitems (tmConst t)    $+$
                               ppitems (tmVar t)      $+$
                               ppitems (tmWire t)     $+$
                               ppitems (tmInit t)     $+$
                               ppitems (tmProcess t)  $+$
                               ppitems (tmMethod t)   $+$
                               ppitems (tmGoal t)     $+$
           text "endtemplate"
        where ppports [] = text ""
              ppports ports = parens $ hsep $ punctuate comma $ map pp ports
              ppitems :: (PP a) => [a] -> Doc
              ppitems = vcat . map ((<> semi) . pp)

instance WithPos Template where
    pos       = tpos
    atPos t p = t{tpos = p}

instance WithName Template where
    name = tname

instance Show Template where
    show = render . pp
