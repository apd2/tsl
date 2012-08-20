{-# LANGUAGE ImplicitParams,UndecidableInstances #-}

module Method(TaskCat(..), 
              MethodCat(..), 
              ArgDir(..), 
              Arg(Arg,argDir), 
              Method(Method,methCat, methArg, methRettyp),
              methVar) where

import Text.PrettyPrint
import Data.Maybe

import Pos
import Name
import Var
import PP
import TypeSpec
import Statement

data TaskCat = Controllable
             | Uncontrollable
             | Invisible
             deriving (Eq)

instance PP TaskCat where
    pp Controllable   = text "controllable"
    pp Uncontrollable = text "uncontrollable"
    pp Invisible      = text "invisible"

data MethodCat = Function
               | Procedure
               | Task TaskCat
               deriving (Eq)

instance PP MethodCat where
    pp Function  = text "function"
    pp Procedure = text "procedure"
    pp (Task c)  = text "task" <+> pp c

instance Show MethodCat where
    show = render . pp

data ArgDir = ArgIn
            | ArgOut
            deriving (Eq)

instance PP ArgDir where
    pp ArgIn  = empty
    pp ArgOut = text "out"

instance Show ArgDir where
    show = render . pp

-- Method argument
data Arg = Arg { apos   :: Pos
               , argDir :: ArgDir
               , atyp   :: TypeSpec
               , aname  :: Ident}

instance PP Arg where
    pp a = pp (argDir a) <+> pp (typ a) <+> pp (name a)

instance WithName Arg where
    name = aname

instance WithPos Arg where
    pos       = apos
    atPos a p = a{apos = p}

instance WithType Arg where 
    typ = atyp

-- Method
data Method = Method { mpos       :: Pos
                     , methExport :: Bool
                     , methCat    :: MethodCat
                     , methRettyp :: Maybe TypeSpec
                     , mname      :: Ident
                     , methArg    :: [Arg]
                     , methBody   :: Either (Maybe Statement, Maybe Statement) Statement}

methVar :: Method -> [Var]
methVar m = case methBody m of
                 Left (b,a) -> concat $ map stmtVar $ (maybeToList b) ++ (maybeToList a)
                 Right s    -> stmtVar s

instance PP Method where
    pp m = (if (methExport m) then text "export" else empty) <+> (pp $ methCat m) <+> 
           (case methRettyp m of 
                 Nothing -> text "void"
                 Just t  -> pp t) <+> 
           (pp $ name m) <+> 
           (parens $ hsep $ punctuate comma $ map pp (methArg m)) $+$
           case methBody m of
                Left (bef,aft) -> case bef of 
                                       Nothing -> empty
                                       Just s -> text "before" $+$ pp s
                                  $+$
                                  case aft of
                                       Nothing -> empty
                                       Just s -> text "after" $+$ pp s
                Right s -> pp s

instance WithName Method where
    name = mname

instance WithPos Method where
    pos       = mpos
    atPos m p = m{mpos = p}
