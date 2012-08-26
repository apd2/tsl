{-# LANGUAGE ImplicitParams, FlexibleContexts, MultiParamTypeClasses, UndecidableInstances, TupleSections, TypeSynonymInstances, FlexibleInstances #-}

module NS(Scope(..),
          WithScope(..),
          Type(Type),
          WithType(..),
          lookupTemplate, checkTemplate, getTemplate, 
          lookupTypeDecl, checkTypeDecl, getTypeDecl,
          lookupTerm    , checkTerm    , getTerm,
          lookupMethod  , checkMethod  , getMethod,
          lookupGoal    , checkGoal    , getGoal,
          Obj(..), objLookup, objGet) where

import Control.Monad.Error
import Data.List
import Data.Maybe
import qualified Data.Map as M
import Text.PrettyPrint

import Util hiding(name)
import PP
import TSLUtil
import Pos
import Name
import Template
import Process
import Method
import Var
import Const
import TypeSpec
import Spec
import Expr

data Scope = ScopeTop
           | ScopeTemplate {scopeTm::Template}
           | ScopeMethod   {scopeTm::Template, scopeMeth::Method}
           | ScopeProcess  {scopeTm::Template, scopeProc::Process}

instance Eq Scope where
    (==) ScopeTop             ScopeTop             = True
    (==) (ScopeTemplate t1)   (ScopeTemplate t2)   = name t1 == name t2
    (==) (ScopeMethod t1 m1)  (ScopeMethod t2 m2)  = name t1 == name t2 && name m1 == name m2
    (==) (ScopeProcess t1 p1) (ScopeProcess t2 p2) = name t1 == name t2 && name p1 == name p2
    (==) _                    _                    = False

class WithScope a where
    scope :: a -> Scope

data Type = Type Scope TypeSpec

instance WithScope Type where
    scope (Type s t) = s

instance WithTypeSpec Type where
    tspec (Type s t) = t

instance (?spec::Spec) => PP Type where
    pp t = case tspec t of
                UserTypeSpec _ n    -> let (d,s) = getTypeDecl (scope t) n
                                       in case s of
                                               ScopeTop         -> text $ sname d
                                               ScopeTemplate tm -> text (sname tm) <> text "::" <> text (sname d)
                StructSpec _   fs   -> text "struct" <+> 
                                       (braces $ nest' $ vcat $ map ((<> semi) . (\f -> pp (Type (scope t) (tspec f)) <+> pp (name f))) fs)
                PtrSpec _      pt   -> pp (Type (scope t) pt) <> char '*'
                ArraySpec _    at l -> pp (Type (scope t) at) <> (brackets $ pp l)
                _                   -> pp $ tspec t

instance (?spec::Spec) => Show Type where
    show = render . pp

class WithType a where
    typ :: a -> Type

instance WithType Type where
    typ = id


-- TSL specification objects

data Obj = ObjSpec
         | ObjTemplate Template
         | ObjPort     Template Port
         | ObjInstance Template Instance
         | ObjProcess  Template Process
         | ObjMethod   Template Method
         | ObjVar      Scope    Var
         | ObjGVar     Template GVar
         | ObjArg      Scope    Arg
         | ObjType              Type
         | ObjTypeDecl Scope    TypeDecl
         | ObjConst    Scope    Const
         | ObjEnum     Type     Enumerator

instance WithPos Obj where
    pos ObjSpec             = error $ "Requesting position of ObjSpec"
    pos (ObjTemplate   t)   = pos t
    pos (ObjPort     _ p)   = pos p
    pos (ObjInstance _ i)   = pos i
    pos (ObjProcess  _ p)   = pos p
    pos (ObjMethod   _ m)   = pos m
    pos (ObjVar      _ v)   = pos v
    pos (ObjGVar     _ v)   = pos v
    pos (ObjArg      _ a)   = pos a
    pos (ObjType       t)   = pos $ tspec t
    pos (ObjTypeDecl _ t)   = pos t
    pos (ObjConst    _ c)   = pos c
    pos (ObjEnum     _ e)   = pos e
    atPos _ = error $ "Not implemented: atPos Obj"

instance WithScope Obj where
    scope ObjSpec           = error $ "requesting scope of ObjSpec"
    scope (ObjTemplate _)   = ScopeTop
    scope (ObjPort t _)     = ScopeTemplate t
    scope (ObjInstance t _) = ScopeTemplate t
    scope (ObjProcess t _)  = ScopeTemplate t
    scope (ObjMethod t m)   = ScopeTemplate t
    scope (ObjVar s _)      = s
    scope (ObjGVar t _)     = ScopeTemplate t
    scope (ObjArg s _)      = s
    scope (ObjType t)       = scope t
    scope (ObjTypeDecl s _) = s
    scope (ObjConst s _)    = s
    scope (ObjEnum t _)     = scope t
    
instance WithName Obj where
    name ObjSpec           = error $ "requesting name of ObjSpec"
    name (ObjTemplate t)   = name t
    name (ObjPort     _ p) = name p
    name (ObjInstance _ i) = name i
    name (ObjProcess  _ p) = name p
    name (ObjMethod   _ m) = name m
    name (ObjVar      _ v) = name v
    name (ObjGVar     _ v) = name v
    name (ObjArg      _ a) = name a
    name (ObjType       t) = error $ "requesting name of a TypeSpec"
    name (ObjTypeDecl _ t) = name t
    name (ObjConst    _ c) = name c
    name (ObjEnum     _ e) = name e

instance (?spec::Spec) => WithType Obj where
    typ (ObjTemplate   t) = error $ "requesting type of ObjTemplate"
    typ (ObjPort     s p) = Type ScopeTop $ TemplateTypeSpec (pos $ getTemplate $ portTemplate p) $ portTemplate p
    typ (ObjInstance s i) = Type ScopeTop $ TemplateTypeSpec (pos $ getTemplate $ instTemplate i) $ instTemplate i
    typ (ObjProcess  _ p) = error $ "requesting type of ObjProcess"
    typ (ObjMethod   _ m) = error $ "requesting type of ObjMethod"
    typ (ObjVar      s v) = Type s $ tspec v
    typ (ObjGVar     t v) = Type (ScopeTemplate t) (tspec v)
    typ (ObjArg      s a) = Type s $ tspec a
    typ (ObjType       t) = error $ "requesting type of ObjType"
    typ (ObjTypeDecl _ d) = error $ "requesting type of ObjTypeDecl"
    typ (ObjConst    s c) = Type s $ tspec c
    typ (ObjEnum     t e) = t

instance (?spec::Spec) => WithTypeSpec Obj where
    tspec = tspec . typ


objLookup :: (?spec::Spec) => Obj -> Ident -> Maybe Obj
objLookup ObjSpec n = listToMaybe $ catMaybes $ [t,d,c]
    where s = ScopeTop
          d = fmap (ObjTypeDecl s)   $ find ((== n) . name) (specType ?spec)
          c = fmap (ObjConst    s)   $ find ((== n) . name) (specConst ?spec)
          t = fmap ObjTemplate       $ find ((== n) . name) (specTemplate ?spec)
          e = fmap (uncurry ObjEnum) $ find ((== n) . name . snd) (concat $ map (\d -> case tspec d of
                                                                                            EnumSpec _ es -> map (Type s (tspec d),) es
                                                                                            _             -> []) $ 
                                                                                specType ?spec)

objLookup (ObjTemplate t) n = listToMaybe $ catMaybes $ [p,v,pr,m,d,c,e,par]
    where -- search for the name in the local scope
          s = ScopeTemplate t
          p  = fmap (ObjPort     t) $ find ((== n) . name) (tmPort t)
          v  = fmap (ObjGVar     t) $ find ((== n) . name) (tmVar t)
          i  = fmap (ObjInstance t) $ find ((== n) . name) (tmInst t)
          pr = fmap (ObjProcess  t) $ find ((== n) . name) (tmProcess t)
          m  = fmap (ObjMethod   t) $ find ((== n) . name) (tmMethod t) 
          d  = fmap (ObjTypeDecl s) $ find ((== n) . name) (tmTypeDecl t)
          c  = fmap (ObjConst    s) $ find ((== n) . name) (tmConst t)
          e  = fmap (uncurry ObjEnum) $ find ((== n) . name . snd) (concat $ map (\d -> case tspec d of
                                                                                             EnumSpec _ es -> map (Type s (tspec d),) es
                                                                                             _             -> []) $ 
                                                                                 tmTypeDecl t)
          -- search parent templates
          par = listToMaybe $ catMaybes $ map (\d -> objLookup (ObjTemplate $ getTemplate $ drvTemplate d) n) (tmDerive t)

objLookup (ObjPort _ p)     n = case objLookup ObjSpec (portTemplate p) of
                                     Just o@(ObjTemplate _)  -> objLookup o n
                                     Nothing                 -> Nothing
objLookup (ObjInstance _ i) n = case objLookup ObjSpec (instTemplate i) of
                                     Just o@(ObjTemplate _)  -> objLookup o n
                                     Nothing                 -> Nothing
objLookup (ObjProcess t p)  n = fmap (ObjVar (ScopeProcess t p)) $ find ((== n) . name) (procVar p)

objLookup (ObjMethod t m)   n = listToMaybe $ catMaybes $ [v,a]
    where v = fmap (ObjVar (ScopeMethod t m)) $ find ((== n) . name) (methVar m)
          a = fmap (ObjArg (ScopeMethod t m)) $ find ((== n) . name) (methArg m)

objLookup o@(ObjVar s v)      n = objLookup o n
objLookup o@(ObjGVar t v)     n = objLookup o n
objLookup o@(ObjArg s a)      n = objLookup o n
objLookup o@(ObjTypeDecl s t) n = objLookup o n

objLookup (ObjType (Type s (StructSpec _ fs))) n = fmap (ObjType . Type s . tspec) $ find ((==n) . name) fs

objLookup (ObjType (Type s (TemplateTypeSpec _ tn))) n = case objLookup ObjSpec tn of
                                                              Just o@(ObjTemplate _) -> objLookup o n
                                                              Nothing                -> Nothing
objLookup (ObjType (Type s (UserTypeSpec _ tn))) n = case lookupTypeDecl s tn of
                                                          Just (d,s') -> objLookup (ObjTypeDecl s' d) n
                                                          Nothing     -> Nothing

objGet :: (?spec::Spec) => Obj -> Ident -> Obj
objGet o n = fromJustMsg ("objLookup failed: " ++ show n) $ objLookup o n

objLookupPath :: (?spec::Spec) => Obj -> [Ident] -> Maybe Obj
objLookupPath o []     = Just o
objLookupPath o (n:ns) = case objLookup o n of
                              Nothing -> Nothing
                              Just o' -> objLookupPath o' ns



-- Lookup identifier visible in the local scope
lookupIdent :: (?spec::Spec) => Scope -> Ident -> Maybe Obj
lookupIdent ScopeTop n          = objLookup ObjSpec n
lookupIdent (ScopeTemplate t) n = listToMaybe $ catMaybes [tm,global]
    where tm     = objLookup (ObjTemplate t) n
          global = objLookup ObjSpec n
lookupIdent (ScopeMethod t m) n = listToMaybe $ catMaybes [local,tm,global]
    where local  = objLookup (ObjMethod t m) n
          tm     = objLookup (ObjTemplate t) n
          global = objLookup ObjSpec n
lookupIdent (ScopeProcess t p) n = listToMaybe $ catMaybes [local,tm,global]
    where local  = objLookup (ObjProcess t p) n
          tm     = objLookup (ObjTemplate t) n
          global = objLookup ObjSpec n

-- Lookup path from the local scope
lookupPath :: (?spec::Spec) => Scope -> [Ident] -> Maybe Obj
lookupPath s (n:ns) = case lookupIdent s n of
                           Nothing -> Nothing
                           Just o  -> objLookupPath o ns

-- Lookup name in the global namespace
lookupGlobal :: (?spec::Spec) => [Ident] -> Maybe Obj
lookupGlobal ns = objLookupPath ObjSpec ns

lookupTemplate :: (?spec::Spec) => Ident -> Maybe Template
lookupTemplate n = case objLookup ObjSpec n of
                        Just (ObjTemplate t) -> Just t
                        _                    -> Nothing
getTemplate :: (?spec::Spec) => Ident -> Template
getTemplate n = fromJustMsg ("getTemplate failed: " ++ show n) $ lookupTemplate n

checkTemplate :: (?spec::Spec, MonadError String me) => Ident -> me (Template)
checkTemplate n = do
    case lookupTemplate n of
         Nothing -> err (pos n) $ "Unknown template name: " ++ (show n)
         Just t  -> return t

-- Type lookup

lookupTypeLocal :: (?spec::Spec) => Scope -> Ident -> Maybe TypeDecl
lookupTypeLocal ScopeTop          n = find ((==n) . name) (specType ?spec)
lookupTypeLocal (ScopeTemplate t) n = find ((==n) . name) (tmTypeDecl t)

lookupTypeDecl :: (?spec::Spec) => Scope -> StaticSym -> Maybe (TypeDecl,Scope)
lookupTypeDecl ScopeTop [n]            = fmap (,ScopeTop) $ lookupTypeLocal ScopeTop n
lookupTypeDecl ScopeTop sn@(n:[n'])    = case objLookup ObjSpec n of
                                               Just o@(ObjTemplate t) -> fmap (,ScopeTemplate t) $ lookupTypeLocal (ScopeTemplate t) n'
                                               Nothing -> Nothing
lookupTypeDecl s@(ScopeTemplate t) [n] = case lookupTypeLocal s n of
                                              Nothing -> fmap (,ScopeTop) $ lookupTypeLocal ScopeTop n
                                              Just t  -> Just (t, s)
lookupTypeDecl (ScopeMethod t _) ns    = lookupTypeDecl (ScopeTemplate t) ns
lookupTypeDecl (ScopeProcess t _) ns   = lookupTypeDecl (ScopeTemplate t) ns
lookupTypeDecl _                 _     = Nothing

checkTypeDecl :: (?spec::Spec, MonadError String me ) => Scope -> StaticSym -> me (TypeDecl,Scope)
checkTypeDecl s n = do
    case lookupTypeDecl s n of
       Nothing -> err (pos n) $ "Unknown type: " ++ (show n)
       Just t  -> return t


getTypeDecl :: (?spec::Spec) => Scope -> StaticSym -> (TypeDecl,Scope)
getTypeDecl s = fromJustMsg "getTypeDecl: type not found" . lookupTypeDecl s

-- Term lookup
-- A term is either a local name, which corresponds to any object in the local or
-- containing scope, or a global name (more than one ::-separate identifiers), which
-- must refer to a constant or enum name.
lookupTerm :: (?spec::Spec) => Scope -> StaticSym -> Maybe Obj

lookupTerm s [n] = lookupIdent s n
lookupTerm s ns = 
    case lookupGlobal ns of
         Just o@(ObjConst _ _) -> Just o
         Just o@(ObjEnum  _ _) -> Just o
         _                     -> Nothing

checkTerm :: (?spec::Spec, MonadError String me) => Scope -> StaticSym -> me Obj
checkTerm s n = case lookupTerm s n of 
                     Nothing -> err (pos n) $ "Unknown term " ++ show n
                     Just t  -> return t

getTerm :: (?spec::Spec) => Scope -> StaticSym -> Obj
getTerm s n = fromJustMsg "getTerm: term lookup failed" $ lookupTerm s n 

-- Method lookup
lookupMethod :: (?spec::Spec) => Scope -> MethodRef -> Maybe (Method, Scope)
lookupMethod s (MethodRef _ p) = case lookupPath s p of
                                      Just (ObjMethod t m) -> Just (m, ScopeTemplate t)
                                      _                    -> Nothing

checkMethod :: (?spec::Spec, MonadError String me) => Scope -> MethodRef -> me (Method, Scope)
checkMethod s m = case lookupMethod s m of
                       Just x  -> return x
                       Nothing -> err (pos m) $ "Unknown method " ++ show m

getMethod :: (?spec::Spec) => Scope -> MethodRef -> (Method, Scope)
getMethod s m = fromJustMsg "getMethod: method not found" $ lookupMethod s m

-- Goal lookup
lookupGoal :: (?spec::Spec) => Scope -> Ident -> Maybe Goal
lookupGoal s n = find ((==n) . name) (tmGoal t)
    where t = case s of
                  ScopeTemplate tm   -> tm
                  ScopeMethod   tm _ -> tm
                  ScopeProcess  tm _ -> tm

checkGoal :: (?spec::Spec, MonadError String me) => Scope -> Ident -> me Goal
checkGoal s n = case lookupGoal s n of
                     Just g  -> return g
                     Nothing -> err (pos n) $ "Unknown goal " ++ show n

getGoal :: (?spec::Spec) => Scope -> Ident -> Goal
getGoal s n = fromJustMsg "getGoal: goal not found" $ lookupGoal s n
