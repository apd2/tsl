{-# LANGUAGE ImplicitParams, FlexibleContexts, MultiParamTypeClasses, UndecidableInstances #-}

module NS(Obj(..), objLookup, objGet) where

import Data.List
import Data.Maybe

import Util hiding(name)
import Pos
import Name
import Template
import Process
import Method
import Var
import Const
import TypeSpec
import Spec

-- Runtime objects

data Obj = ObjTemplate Template
         | ObjPort     Port
         | ObjInstance Instance
         | ObjProcess  Process
         | ObjMethod   Method
         | ObjVar      Var
         | ObjGVar     GVar
         | ObjArg      Arg
         | ObjType     TypeSpec
         | ObjTypeDecl TypeDecl
         | ObjConst    Const
         | ObjEnum     Enumerator

instance WithPos Obj where
    pos (ObjTemplate t) = pos t
    pos (ObjPort     p) = pos p
    pos (ObjInstance i) = pos i
    pos (ObjProcess  p) = pos p
    pos (ObjMethod   m) = pos m
    pos (ObjVar      v) = pos v
    pos (ObjGVar     v) = pos v
    pos (ObjArg      a) = pos a
    pos (ObjType     t) = pos t
    pos (ObjTypeDecl t) = pos t
    pos (ObjConst    c) = pos c
    pos (ObjEnum     e) = pos e
    atPos _ = error $ "Not implemented: atPos Obj"


instance WithName Obj where
    name (ObjTemplate t) = name t
    name (ObjPort     p) = name p
    name (ObjInstance i) = name i
    name (ObjProcess  p) = name p
    name (ObjMethod   m) = name m
    name (ObjVar      v) = name v
    name (ObjGVar     v) = name v
    name (ObjArg      a) = name a
    name (ObjType     t) = error $ "requesting name of a TypeSpec"
    name (ObjTypeDecl t) = name t
    name (ObjConst    c) = name c
    name (ObjEnum     e) = name e


objLookup :: (?spec::Spec) => Obj -> Ident -> Maybe Obj
objLookup (ObjTemplate t) n = listToMaybe $ catMaybes $ [p,v,pr,m,d,c,e,par]
    where -- search for the name in the local scope
          p  = fmap ObjPort     $ find ((== n) . name) (tmPort t)
          v  = fmap ObjGVar     $ find ((== n) . name) (tmVar t)
          i  = fmap ObjInstance $ find ((== n) . name) (tmInst t)
          pr = fmap ObjProcess  $ find ((== n) . name) (tmProcess t)
          m  = fmap ObjMethod   $ find ((== n) . name) (tmMethod t) 
          d  = fmap ObjTypeDecl $ find ((== n) . name) (tmTypeDecl t)
          c  = fmap ObjConst    $ find ((== n) . name) (tmConst t)
          e  = fmap ObjEnum     $ find ((== n) . name) (concat $ map (\t -> case typ t of
                                                                                 EnumSpec _ es -> es
                                                                                 _             -> []) $ 
                                                                     tmTypeDecl t)
          -- search parent templates
          par = listToMaybe $ catMaybes $ map (\d -> objLookup (ObjTemplate $ specGetTemplate $ drvTemplate d) n) (tmDerive t)

objLookup (ObjPort p)     n = case specLookupTemplate (portTemplate p) of
                                   Nothing -> Nothing
                                   Just t  -> objLookup (ObjTemplate t) n
objLookup (ObjInstance i) n = case specLookupTemplate (instTemplate i) of
                                   Nothing -> Nothing
                                   Just t  -> objLookup (ObjTemplate t) n
objLookup (ObjProcess p)  n = fmap ObjVar $ find ((== n) . name) (procVar p)

objLookup (ObjMethod m)   n = listToMaybe $ catMaybes $ [v,a]
    where v  = fmap ObjVar $ find ((== n) . name) (methVar m)
          a  = fmap ObjArg $ find ((== n) . name) (methArg m)

objLookup (ObjVar v)      n = objLookup (ObjType $ typ v) n
objLookup (ObjGVar v)     n = objLookup (ObjType $ typ v) n
objLookup (ObjArg a)      n = objLookup (ObjType $ typ a) n
objLookup (ObjTypeDecl t) n = objLookup (ObjType $ typ t) n
objLookup (ObjType (StructSpec _ fs)) n = fmap (ObjType . typ) $ find ((==n) . name) fs

objGet :: (?spec::Spec) => Obj -> Ident -> Obj
objGet o n = fromJustMsg ("objLookup failed: " ++ show n) $ objLookup o n
