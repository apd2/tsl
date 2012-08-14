module Obj() where

import qualified Template as Tm
import qualified Process  as P
import qualified Method   as M
import qualified Var      as V
import qualified Const    as C
import qualified Spec     as S
import qualified TypeSpec as T
import NS

data Obj = ObjTemplate Tm.Template
         | ObjPort     Tm.Port
         | ObjInstance Tm.Instance
         | ObjProcess  P.Process
         | ObjMethod   M.Method
         | ObjVar      V.Var
         | ObjConst    C.Const
         | ObjEnum     T.Enumerator
         | ObjArg      M.Arg
         | ObjType     T.TypeSpec

instance (?spec::S.Spec) => NS Obj Obj where
    lookup (ObjTemplate t) = lookup t
    lookup (ObjPort p)     = lookup p
    lookup (ObjInstance i) = lookup i
    lookup (ObjProcess p)  = lookup p
    lookup (ObjMethod m)   = lookup m
    lookup (ObjVar v)      = lookup v
    lookup (ObjArg a)      = lookup a
    lookup (ObjConst c)    = lookup c
    lookup (ObjType t)     = lookup t
    lookup (ObjEnum _)     = Nothing
