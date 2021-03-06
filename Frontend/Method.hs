{-# LANGUAGE ImplicitParams,UndecidableInstances #-}

module Frontend.Method(TaskCat(..), 
              MethodCat(..), 
              ArgDir(..), 
              Arg(Arg,argDir,argTSpec), 
              Method(Method,methExport, methCat, methArg, methRettyp, methName),
              methVar,
              methBody,
              methIsVirtual) where

import Text.PrettyPrint
import Data.Maybe

import Pos
import Name
import Frontend.TVar
import PP
import Frontend.Type
import Frontend.Statement

data TaskCat = Controllable
             | Uncontrollable
             | Invisible
             deriving (Eq)

instance PP TaskCat where
    pp Controllable   = text "controllable"
    pp Uncontrollable = text "uncontrollable"
    pp Invisible      = empty

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
data Arg = Arg { apos     :: Pos
               , argDir   :: ArgDir
               , argTSpec :: TypeSpec
               , aname    :: Ident}

instance PP Arg where
    pp a = pp (argDir a) <+> pp (tspec a) <+> pp (name a)

instance WithName Arg where
    name = aname

instance WithPos Arg where
    pos       = apos
    atPos a p = a{apos = p}

instance WithTypeSpec Arg where 
    tspec = argTSpec

-- Method
data Method = Method { mpos       :: Pos
                     , methExport :: Bool
                     , methCat    :: MethodCat
                     , methRettyp :: Maybe TypeSpec
                     , methName   :: Ident
                     , methArg    :: [Arg]
                     , methBody   :: Either (Maybe Statement, Maybe Statement) Statement}

-- use methFullVar for complete list of local vars
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
    name = methName

instance WithPos Method where
    pos       = mpos
    atPos m p = m{mpos = p}

instance Show Method where
    show      = render . pp

methIsVirtual :: Method -> Bool
methIsVirtual m = case methBody m of
                       Left _  -> True
                       Right _ -> False

