{-# LANGUAGE ImplicitParams,UndecidableInstances #-}

module Method(TaskCat(..), 
              MethodCat(..), 
              ArgDir(..), 
              Arg(argDir), 
              Method(methCat, methVar, methArg)) where

import Pos
import Name
import Var
import TypeSpec

data TaskCat = Controllable
             | Uncontrollable
             | Invisible

data MethodCat = Function
               | Procedure
               | Task TaskCat

data ArgDir = In
            | Out

-- Method argument
data Arg = Arg { apos   :: Pos
               , aname  :: Ident
               , atyp   :: TypeSpec
               , argDir :: ArgDir}

instance WithName Arg where
    name = aname

instance WithPos Arg where
    pos = apos

instance WithType Arg where 
    typ = atyp

-- Method
data Method = Method { mpos    :: Pos
                     , mname   :: Ident
                     , methCat :: MethodCat
                     , rettyp  :: TypeSpec
                     , methArg :: [Arg]
                     , methVar :: [Var]}

instance WithName Method where
    name = mname

instance WithPos Method where
    pos = mpos

instance WithType Method where
    typ = rettyp
