{-# LANGUAGE ImplicitParams, FlexibleContexts, MultiParamTypeClasses, UndecidableInstances #-}

module Obj(Obj(..)) where

import Prelude hiding (lookup)
import Data.List hiding (lookup)
import Data.Maybe

import Name
import qualified Template as Tm
import qualified Process  as P
import qualified Method   as M
import qualified Var      as V
import qualified Const    as C
import qualified TypeSpec as T
import qualified Spec     as S
import qualified NS

-- Runtime objects

data Obj = ObjTemplate Tm.Template
         | ObjPort     Tm.Port
         | ObjInstance Tm.Instance
         | ObjProcess  P.Process
         | ObjMethod   M.Method
         | ObjVar      V.Var
         | ObjArg      M.Arg
         | ObjType     T.TypeSpec
         
class (NS.NS a Obj) => ObjNS a where
    (!) :: a -> Ident -> Obj
    (!) = (NS.!)
    (!!) :: a -> [Ident] -> Obj
    (!!) = (NS.!!)

instance (?spec::S.Spec) => NS.NS Obj Obj where
    lookup (ObjTemplate t) = NS.lookup t
    lookup (ObjPort p)     = NS.lookup p
    lookup (ObjInstance i) = NS.lookup i
    lookup (ObjProcess p)  = NS.lookup p
    lookup (ObjMethod m)   = NS.lookup m
    lookup (ObjVar v)      = NS.lookup v
    lookup (ObjArg a)      = NS.lookup a
    lookup (ObjType t)     = NS.lookup t
    rlookup o []           = Just o
    rlookup o (i:is)       = case (NS.lookup o i)::(Maybe Obj) of
                                  Nothing -> Nothing
                                  Just o' -> NS.rlookup o' is

instance (?spec::S.Spec) => ObjNS Obj


instance NS.NS T.TypeSpec Obj where
    lookup (T.StructSpec _ fs) n = fmap (ObjType . snd) $ find ((==n) . fst) fs
    lookup _ _                 = Nothing

instance ObjNS T.TypeSpec

instance NS.NS P.Process Obj where
    lookup p n = fmap ObjVar $ find ((== n) . name) (P.var p)

instance ObjNS P.Process

instance NS.NS V.Var Obj where
    lookup v = NS.lookup (T.typ v)

instance ObjNS V.Var

instance NS.NS M.Arg Obj where
    lookup a = NS.lookup (T.typ a)

instance ObjNS M.Arg

instance NS.NS M.Method Obj where
    lookup m n = listToMaybe [v,a]
        where -- search for the name in the local scope
              v  = fmap ObjVar $ find ((== n) . name) (M.var m)
              a  = fmap ObjArg $ find ((== n) . name) (M.arg m)

instance ObjNS M.Method

instance (?spec::S.Spec) => NS.NS Tm.Template Obj where
    lookup t n = listToMaybe [p,v,i,pr,m,par]
        where -- search for the name in the local scope
              p  = fmap ObjPort     $ find ((== n) . name) (Tm.port t)
              v  = fmap ObjVar      $ find ((== n) . name) (Tm.var t)
              i  = fmap ObjInstance $ find ((== n) . name) (Tm.inst t)
              pr = fmap ObjProcess  $ find ((== n) . name) (Tm.process t)
              m  = fmap ObjMethod   $ find ((== n) . name) (Tm.method t) 
              -- search parent templates
              par = listToMaybe $ map (\d -> NS.lookup d n) (Tm.derive t)

instance ObjNS Tm.Template

instance (?spec::S.Spec) => NS.NS Tm.Port Obj where
    lookup p i   = fmap (\t -> NS.lookup t i) (S.lookupTemplate ?spec (Tm.portTemplate p))
    rlookup p is = fmap (\t -> NS.rlookup t is) (S.lookupTemplate ?spec (Tm.portTemplate p))

instance ObjNS Tm.Port

instance (?spec::S.Spec) => NS.NS Tm.Instance Obj where
    lookup inst i   = fmap (\t -> NS.lookup t i) (S.lookupTemplate ?spec (Tm.instTemplate inst))
    rlookup inst is = fmap (\t -> NS.rlookup t is) (S.lookupTemplate ?spec (Tm.instTemplate inst))

instance ObjNS Tm.Instance


instance (?spec::S.Spec) => NS.NS Tm.Derive Obj where
    lookup d i   = fmap (\t -> NS.lookup t i) (S.lookupTemplate ?spec (Tm.drvTemplate d))
    rlookup d is = fmap (\t -> NS.rlookup t is) (S.lookupTemplate ?spec (Tm.drvTemplate d))

instance ObjNS Tm.Derive
