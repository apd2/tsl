module Method(TaskCat(..), MethodCat(..), ArgDir(..), Arg, Method) where

import Pos
import Name
import qualified Var      as V
import qualified TypeSpec as T

data TaskCat = Controllable
             | Uncontrollable
             | Invisible

data MethodCat = Function
               | Procedure
               | Task TaskCat

data ArgDir = In
            | Out

-- Method argument
data Arg = Arg { apos  :: Pos
               , aname :: Ident
               , atyp  :: T.TypeSpec
               , dir   :: ArgDir}

instance WithName Arg where
    name = aname

instance WithPos Arg where
    pos = apos

instance WithType Arg where 
    typ = typ . atyp

instance NS Arg Obj where
    lookup a = lookup (atyp a)


-- Method
data Method = Method { mpos   :: Pos
                     , mname  :: Ident
                     , cat    :: MethodCat
                     , rettyp :: T.TypeSpec
                     , arg    :: [Arg]
                     , var    :: [V.Var]}

instance WithName Method where
    name = mname

instance WithPos Method where
    pos = mpos

instance WithType Method where
    typ = typ . rettyp

instance NS Method Obj where
    lookup m (Field n) = listToMaybe [v,a]
        where -- search for the name in the local scope
              v  = fmap ObjVar $ find ((== n) . name) (var m)
              a  = fmap ObjArg $ find ((== n) . name) (arg m)

    lookup m _ = Nothing
