{-# LANGUAGE ImplicitParams, FlexibleContexts, TupleSections #-}

module StatementOps(mapStat,
                    mapStatM,
                    statMapExpr,
                    statMapTSpec,
                    statCallees,
                    statSubprocessRec,
                    statSubprocessNonrec,
                    statFlatten,
                    statObjs,
                    statObjsRec,
                    methObjsRec,
                    statReturns,
                    validateStat,
                    validateStat') where

import Control.Monad.Error
import Data.Maybe
import Data.List
import Debug.Trace
import qualified Data.Traversable as Tr

import TSLUtil
import Util hiding (name, trace)
import Pos
import Name
import Expr
import {-# SOURCE #-} ExprOps
import ExprFlatten
import ExprValidate
import Spec
import NS
import Statement
import Type
import TypeOps
import TVar
import TVarOps
import Method
import Template
import InstTree

-- Map function over all substatements
mapStat :: (?spec::Spec) => (Scope -> Statement -> Statement) -> Scope -> Statement -> Statement
mapStat f s (SSeq     p l ss)        = f s $ SSeq     p l (map (mapStat f s) ss)
mapStat f s (SPar     p l ss)        = f s $ SPar     p l (map (mapStat f s) ss)
mapStat f s (SForever p l b)         = f s $ SForever p l (mapStat f s b)
mapStat f s (SDo      p l b c)       = f s $ SDo      p l (mapStat f s b) c
mapStat f s (SWhile   p l c b)       = f s $ SWhile   p l c (mapStat f s b)
mapStat f s (SFor     p l (i,c,u) b) = f s $ SFor     p l ((fmap (mapStat f s) i),c, mapStat f s u) (mapStat f s b)
mapStat f s (SChoice  p l ss)        = f s $ SChoice  p l (map (mapStat f s) ss)
mapStat f s (SITE     p l c t me)    = f s $ SITE     p l c (mapStat f s t) (fmap (mapStat f s) me)
mapStat f s (SCase    p l c cs md)   = f s $ SCase    p l c (map (\(e,st) -> (e,mapStat f s st)) cs) (fmap (mapStat f s) md)
mapStat f s st                       = f s st

mapStatM :: (Monad m, ?spec::Spec) => (Scope -> Statement -> m Statement) -> Scope -> Statement -> m Statement
mapStatM f s (SSeq     p l ss)        = f s =<< (liftM  $ SSeq     p l)       (mapM (mapStatM f s) ss)
mapStatM f s (SPar     p l ss)        = f s =<< (liftM  $ SPar     p l)       (mapM (mapStatM f s) ss)
mapStatM f s (SForever p l b)         = f s =<< (liftM  $ SForever p l)       (mapStatM f s b)
mapStatM f s (SDo      p l b c)       = f s =<< (liftM  $ (flip $ SDo p l) c) (mapStatM f s b)
mapStatM f s (SWhile   p l c b)       = f s =<< (liftM  $ SWhile   p l c)     (mapStatM f s b)
mapStatM f s (SFor     p l (i,c,u) b) = do i' <- Tr.sequence $ fmap (mapStatM f s) i
                                           u' <- mapStatM f s u
                                           b' <- mapStatM f s b
                                           f s $ SFor p l (i', c, u') b'
mapStatM f s (SChoice  p l ss)        = f s =<< (liftM  $ SChoice  p l)       (mapM (mapStatM f s) ss)
mapStatM f s (SITE     p l c t me)    = f s =<< (liftM2 $ SITE     p l c)     (mapStatM f s t) (Tr.sequence $ fmap (mapStatM f s) me)
mapStatM f s (SCase    p l c cs md)   = do cs' <- mapM (\(e,st) -> do st' <- mapStatM f s st
                                                                      return (e,st')) cs
                                           md' <- Tr.sequence $ fmap (mapStatM f s) md
                                           f s $ SCase p l c cs' md'
mapStatM f s st                       = f s st


-- Map function over all TypeSpec's in the statement
statMapTSpec :: (?spec::Spec) => (Scope -> TypeSpec -> TypeSpec) -> Scope -> Statement -> Statement
statMapTSpec f s st = mapStat (statMapTSpec' f) s st

statMapTSpec' :: (?spec::Spec) => (Scope -> TypeSpec -> TypeSpec) -> Scope -> Statement -> Statement
statMapTSpec' f s (SVarDecl p l v) = SVarDecl p l (Var (pos v) (varMem v) (mapTSpec f s $ tspec v) (name v) (varInit v))
statMapTSpec' _ _ st               = st

-- Map function over all expressions in the statement
statMapExpr :: (?spec::Spec) => (Scope -> Expr -> Expr) -> Scope -> Statement -> Statement
statMapExpr f s st = mapStat (statMapExpr' f) s st

statMapExpr' :: (?spec::Spec) =>  (Scope -> Expr -> Expr) -> Scope -> Statement -> Statement
statMapExpr' f s (SVarDecl p l v)            = SVarDecl p l (varMapExpr f s v)
statMapExpr' f s (SReturn  p l mr)           = SReturn  p l (fmap (mapExpr f s) mr)
statMapExpr' f s (SDo      p l b c)          = SDo      p l b (mapExpr f s c)
statMapExpr' f s (SWhile   p l c b)          = SWhile   p l (mapExpr f s c) b
statMapExpr' f s (SFor     p l (i,c,u) b)    = SFor     p l (i, mapExpr f s c, u) b
statMapExpr' f s (SInvoke  p l m mas)        = SInvoke  p l m (map (fmap $ mapExpr f s) mas)
statMapExpr' f s (SWait    p l e)            = SWait    p l (mapExpr f s e)
statMapExpr' f s (SAssert  p l e)            = SAssert  p l (mapExpr f s e)
statMapExpr' f s (SAssume  p l e)            = SAssume  p l (mapExpr f s e)
statMapExpr' f s (SAssign  p l lhs rhs)      = SAssign  p l (mapExpr f s lhs) (mapExpr f s rhs)
statMapExpr' f s (SITE     p l c t me)       = SITE     p l (mapExpr f s c) t me
statMapExpr' f s (SCase    p l c cs md)      = SCase    p l (mapExpr f s c) (map (mapFst $ mapExpr f s) cs) md
statMapExpr' f s (SMagic   p l)              = SMagic   p l
statMapExpr' f s st                          = st

-- Find all methods invoked by the statement
statCallees :: (?spec::Spec) => Scope -> Statement -> [(Pos, (Template, Method))]
statCallees s (SVarDecl _ _ v)            = fromMaybe [] $ fmap (exprCallees s) $ varInit v
statCallees s (SReturn  _ _ me)           = fromMaybe [] $ fmap (exprCallees s) me
statCallees s (SSeq     _ _ ss)           = concatMap (statCallees s) ss
statCallees s (SPar     _ _ ss)           = concatMap (statCallees s) ss
statCallees s (SForever _ _ b)            = statCallees s b
statCallees s (SDo      _ _ b c)          = statCallees s b ++ exprCallees s c
statCallees s (SWhile   _ _ c b)          = exprCallees s c ++ statCallees s b
statCallees s (SFor     _ _ (i,c,u) b)    = (fromMaybe [] $ fmap (statCallees s) i) ++ exprCallees s c ++ statCallees s u ++ statCallees s b
statCallees s (SChoice  _ _ ss)           = concatMap (statCallees s) ss
statCallees s (SInvoke  p _ mref mas)     = (p,getMethod s mref):(concatMap (exprCallees s) $ catMaybes mas)
statCallees s (SWait    _ _ e)            = exprCallees s e
statCallees s (SAssert  _ _ e)            = exprCallees s e
statCallees s (SAssume  _ _ e)            = exprCallees s e
statCallees s (SAssign  _ _ l r)          = exprCallees s l ++ exprCallees s r
statCallees s (SITE     _ _ c t me)       = exprCallees s c ++ statCallees s t ++ (fromMaybe [] $ fmap (statCallees s) me)
statCallees s (SCase    _ _ c cs md)      = exprCallees s c ++ 
                                            concatMap (\(e,st) -> exprCallees s e ++ statCallees s st) cs ++
                                            (fromMaybe [] $ fmap (statCallees s) md)
statCallees _ _                           = []


-- Objects referred to by the statement
statObjs :: (?spec::Spec, ?scope::Scope) => Statement -> [Obj]
statObjs (SVarDecl _ _ v)             = (ObjVar ?scope v) : (concatMap exprObjs $ maybeToList $ varInit v)
statObjs (SReturn  _ _ mr)            = concatMap exprObjs $ maybeToList mr
statObjs (SSeq     _ _ ss)            = concatMap statObjs ss
statObjs (SPar     _ _ ps)            = concatMap statObjs ps
statObjs (SForever _ _ s)             = statObjs s
statObjs (SDo      _ _ s c)           = statObjs s ++ exprObjs c
statObjs (SWhile   _ _ c s)           = statObjs s ++ exprObjs c
statObjs (SFor     _ _ (mi, c, i) s)  = statObjs s ++ exprObjs c ++ statObjs i ++ (concatMap statObjs $ maybeToList mi)
statObjs (SChoice  _ _ ss)            = concatMap statObjs ss
statObjs (SInvoke  _ _ m mas)         = (let (t,meth) = getMethod ?scope m in ObjMethod t meth):
                                        (concatMap exprObjs $ catMaybes mas)
statObjs (SWait    _ _ c)             = exprObjs c
statObjs (SAssert  _ _ c)             = exprObjs c
statObjs (SAssume  _ _ c)             = exprObjs c
statObjs (SAssign  _ _ l r)           = exprObjs l ++ exprObjs r
statObjs (SITE     _ _ c t me)        = exprObjs c ++ statObjs t ++ (concatMap statObjs $ maybeToList me)
statObjs (SCase    _ _ c cs md)       = exprObjs c ++
                                        concatMap (\(e,s) -> exprObjs e ++ statObjs s) cs ++
                                        concatMap statObjs (maybeToList md)
statObjs _                            = []

-- recursive version
statObjsRec :: (?spec::Spec, ?scope::Scope) => Statement -> [Obj]
statObjsRec s =
    let os = statObjs s
        mos = filter (\o -> case o of
                                 ObjMethod _ _ -> True
                                 _             -> False) os
        os' = concatMap (\(ObjMethod t m) -> methObjsRec t m) mos
    in os ++ os'

-- Recursively compute objects referenced in the body of the method
methObjsRec :: (?spec::Spec) => Template -> Method -> [Obj]
methObjsRec t m = 
    let ?scope = ScopeMethod t m
    in case methBody m of
            Left (ms1,ms2) -> concatMap statObjsRec $ maybeToList ms1 ++ maybeToList ms2
            Right s        -> statObjsRec s

-- List of subprocesses spawned by the statement:
-- Computed by recursing through fork statements
statSubprocessRec :: (?spec::Spec) => Statement -> [Statement]
statSubprocessRec (SSeq     _ _ ss)         = concatMap statSubprocessRec ss
statSubprocessRec (SPar     _ _ ss)         = ss ++ concatMap statSubprocessRec ss
statSubprocessRec (SForever _ _ b)          = statSubprocessRec b
statSubprocessRec (SDo      _ _ b _)        = statSubprocessRec b
statSubprocessRec (SWhile   _ _ _ b)        = statSubprocessRec b
statSubprocessRec (SFor     _ _ (mi,_,s) b) = concatMap statSubprocessRec $ (maybeToList mi) ++ [s,b]
statSubprocessRec (SChoice  _ _ ss)         = concatMap statSubprocessRec ss
statSubprocessRec (SITE     _ _ _ t me)     = concatMap statSubprocessRec $ t:(maybeToList me)
statSubprocessRec (SCase    _ _ _ cs mdef)  = concatMap statSubprocessRec $ map snd cs ++ maybeToList mdef
statSubprocessRec _                         = []

-- non-recursive (first-level subprocesses only)
statSubprocessNonrec :: (?spec::Spec) => Statement -> [Statement]
statSubprocessNonrec (SSeq     _ _ ss)         = concatMap statSubprocessNonrec ss
statSubprocessNonrec (SPar     _ _ ss)         = ss 
statSubprocessNonrec (SForever _ _ b)          = statSubprocessNonrec b
statSubprocessNonrec (SDo      _ _ b _)        = statSubprocessNonrec b
statSubprocessNonrec (SWhile   _ _ _ b)        = statSubprocessNonrec b
statSubprocessNonrec (SFor     _ _ (mi,_,s) b) = concatMap statSubprocessNonrec $ (maybeToList mi) ++ [s,b]
statSubprocessNonrec (SChoice  _ _ ss)         = concatMap statSubprocessNonrec ss
statSubprocessNonrec (SITE     _ _ _ t me)     = concatMap statSubprocessNonrec $ t:(maybeToList me)
statSubprocessNonrec (SCase    _ _ _ cs mdef)  = concatMap statSubprocessNonrec $ map snd cs ++ maybeToList mdef
statSubprocessNonrec _                         = []


statFlatten :: (?spec::Spec) => IID -> Scope -> Statement -> Statement
statFlatten iid s st = mapStat (statFlatten' iid) s $ statMapExpr (exprFlatten' iid) s st

statFlatten' :: (?spec::Spec) => IID -> Scope -> Statement -> Statement
statFlatten' iid s st = statFlatten'' iid s $ st{stLab = fmap (\l -> itreeFlattenName iid l) $ stLab st}

statFlatten'' :: (?spec::Spec) => IID -> Scope -> Statement -> Statement
statFlatten'' iid s (SInvoke p l (MethodRef p' n) as) = SInvoke p l (MethodRef p' [itreeFlattenName (itreeRelToAbsPath iid (init n)) (last n)]) as
statFlatten'' _   _ st                                = st

-- True if the statement returns a value on all execution paths.
statReturns :: Statement -> Bool
statReturns (SReturn  _ _ r)             = isJust r
statReturns (SSeq     _ _ ss)            = statReturns $ last ss
statReturns (SChoice  _ _  ss)           = all statReturns ss
statReturns (SITE     _ _ _ t (Just e))  = statReturns t && statReturns e
statReturns (SCase    _ _ _ cs (Just d)) = all statReturns (d: (map snd cs))
statReturns _                            = False

-------------------------------------------------------------------------
-- Validation
-------------------------------------------------------------------------

validateStat :: (?spec::Spec, ?privoverride::Bool, MonadError String me) => Scope -> Statement -> me ()
validateStat s st = do let ?scope = s 
                       validateStat' False st

-- The first argument indicates that the statement belongs to a loop
validateStat' :: (?spec::Spec, ?privoverride::Bool, ?scope::Scope, MonadError String me) => Bool -> Statement -> me ()
validateStat' _ (SVarDecl p _ v) = do 
    assert (not $ isTemplateScope ?scope) p "variable declaration inside always-block"
    validateVar ?scope v
    validateVar2 ?scope v

validateStat' _ (SReturn p _ me) = do
    case ?scope of
         ScopeMethod  _ m  -> case methRettyp m of
                                   Nothing -> assert (isNothing me) p "cannot return value from method with void return type"
                                   Just t  -> do assert (isJust me) p "return value not specified"
                                                 checkTypeMatch (Type ?scope t) (fromJust me)
         ScopeProcess _ pr -> assert (isNothing me) p "cannot return value from a process"
         ScopeTemplate _   -> err p "return statement inside always-block"

validateStat' l (SSeq _ _ ss) = do
    mapM (validateStat' l) ss
    return ()

validateStat' l (SPar p _ ss) = do
    mapM (\s -> assert (isJust $ stLab s) (pos s) "unlabelled forked process") ss
    mapM (validateStat' l) ss
    case ?scope of
         ScopeMethod  _ m -> case methCat m of
                                  Function          -> err p "fork inside function"
                                  Procedure         -> err p "fork inside procedure"
                                  Task Controllable -> err p "fork inside controllable task"
                                  _                 -> return ()
         ScopeProcess _ pr -> return ()
         ScopeTemplate _   -> err p $ "fork inside always-block"

validateStat' _ (SForever _ _ b) = do
    checkLoopBody b

validateStat' _ (SDo _ _ b c) = do
    validateExpr' c
    assert (isBool c) (pos c) "loop condition is not of boolean type"
    checkLoopBody b

validateStat' _ (SWhile _ _ c b) = do
    validateExpr' c
    assert (isBool c) (pos c) "loop condition is not of boolean type"
    checkLoopBody b

validateStat' _ (SFor _ _ (mi, c, s) b) = do
    validateExpr' c
    assert (isBool c) (pos c) "loop condition is not of boolean type"
    case mi of
         Just i  -> validateStat' False i
         Nothing -> return ()
    validateStat' False s
    checkLoopBody b

validateStat' l (SChoice p _ ss) = do
    case ?scope of
         ScopeMethod  _ m -> case methCat m of
                                  Function            -> err p "non-deterministic choice inside function"
                                  Procedure           -> err p "non-deterministic choice inside procedure"
                                  Task Uncontrollable -> err p "non-deterministic choice inside uncontrollable task"
                                  _                   -> return ()
         ScopeProcess _ pr -> return ()
         ScopeTemplate _   -> err p "non-deterministic choice inside always-block"
    mapM (validateStat' l) ss
    return ()

validateStat' _ (SPause p _) = do
    case ?scope of
         ScopeMethod  _ m -> case methCat m of
                                  Function          -> err p "pause inside function"
                                  Procedure         -> err p "pause inside procedure"
                                  Task Controllable -> err p "pause inside controllable task"
                                  _                 -> return ()
         ScopeProcess _ pr -> return ()
         ScopeTemplate _   -> err p "pause inside always-block"

validateStat' _ (SStop p _) = do
    case ?scope of
         ScopeMethod  _ m -> case methCat m of
                                  Function          -> err p "stop inside function"
                                  Procedure         -> err p "stop inside procedure"
                                  Task Controllable -> err p "stop inside controllable task"
                                  _                 -> return ()
         ScopeProcess _ pr -> return ()
         ScopeTemplate _   -> err p "stop inside always-block"

validateStat' _ (SWait p _ e) = do
    validateExpr' e
    assert (isBool e) (pos e) "wait condition is not of boolean type"
    -- because we do not handle them correctly during inlining
    assert (null $ exprCallees ?scope e) (pos e) $ "Method invocations not allowed inside wait conditions"
    assert (not $ any (\o -> case o of
                                  ObjWire _ _ -> True
                                  _           -> False) $ exprObjs e) (pos e) $ "Wires not allowed inside wait conditions"
    case ?scope of
         ScopeMethod  _ m -> case methCat m of
                                  Function          -> err p "wait inside function"
                                  Procedure         -> err p "wait inside procedure"
                                  Task Controllable -> err p "wait inside controllable task"
                                  _                 -> return ()
         ScopeProcess _ pr -> return ()
         ScopeTemplate _   -> err p "wait inside always-block"

validateStat' l (SBreak p _) = assert l p "break outside a loop"
validateStat' _ (SInvoke p _ m as) = validateCall p m as
validateStat' _ (SAssert _ _ e) = do
    validateExpr' e
    assert (isBool e) (pos e) "Assertion must be a boolean expression"
    assert (exprNoSideEffects e) (pos e) "Assertion must be side-effect free"
    assert (not $ isFunctionScope ?scope) (pos e) "Assertions not allowed inside functions"
    assert (not $ isTemplateScope ?scope) (pos e) "Assertions not allowed inside always-blocks"

validateStat' _ (SAssume _ _ e) = do
    validateExpr' e
    assert (isBool e) (pos e) "Assumption must be a boolean expression"
    assert (exprNoSideEffects e) (pos e) "Assumption must be side-effect free"

validateStat' _ (SAssign _ _ lhs rhs) = do
    validateExpr' lhs
    validateExpr' rhs
    assert (isLExpr lhs) (pos lhs) $ "Left-hand side of assignment is not an L-value"
    checkTypeMatch lhs rhs
    -- No modifications to global variables in a function
    if isFunctionScope ?scope 
       then assert (isLocalLHS lhs) (pos lhs) "Global state modification inside a function"
       else return ()

validateStat' l (SITE _ _ i t e) = do
    validateExpr' i
    assert (isBool i) (pos i) "Condition of an if-statement must be a boolean expression"
    validateStat' l t
    case e of 
         Just s  -> validateStat' l s
         Nothing -> return ()

validateStat' l (SCase p _ c cs md) = do
    validateExpr' c
    assert (length cs > 0) p "Empty case statement"
    mapM (\(e,s) -> do validateExpr' e
                       validateStat' l s
                       assert (exprNoSideEffects e) (pos e) "Case label must be side-effect free") cs
    case md of
         Just d  -> validateStat' l d
         Nothing -> return ()
    mapM (\(e1,_) -> checkTypeMatch c e1) cs
    return ()

validateStat' l (SMagic p _) = do
    case ?scope of
         ScopeMethod t m -> assert (methCat m == Task Uncontrollable) p "Magic blocks only allowed in uncontrollable tasks"
         _               -> err p "Magic blocks only allowed in uncontrollable tasks"

-- There is no path through the loop body that does not break out of the loop and
-- does not contain some form of pause
checkLoopBody :: (?spec::Spec, ?scope::Scope, ?privoverride::Bool, MonadError String me) => Statement -> me ()
checkLoopBody s = do
    validateStat' True s
    case findInstPath False s of
         Nothing -> return ()
         Just p  -> err (pos s) $ "Instanteneous path exists through the body of the loop:" ++
                                  (concat $ map (\s -> "\n    " ++ case s of 
                                                                        Left st -> spos st ++ ": " ++ show st
                                                                        Right e -> spos e  ++ ": " ++ show e) p)
                                  
-- Find instantaneous path through the statement.  
-- If the first argument is true, then Break is considered
-- instantaneous; otherwise it's not.
findInstPath :: (?spec::Spec, ?scope::Scope) => Bool -> Statement -> Maybe [Either Statement Expr]
findInstPath _     s@(SVarDecl _ _ _)    = Just []
findInstPath _       (SReturn _ _ _)     = Nothing
findInstPath b     s@(SSeq _ _ ss)       = let ps  = map (findInstPath b) ss
                                               ps' = case findIndex (\p -> isJust p && 
                                                                           (not $ null $ fromJust p) && 
                                                                           isBreak (last $ fromJust p)) ps of
                                                          Nothing -> ps
                                                          Just i  -> take (i+1) ps
                                           in if all isJust ps'
                                                 then Just $ concat $ map fromJust ps'
                                                 else Nothing
findInstPath _       (SPar _ _ _)        = Nothing
findInstPath _       (SForever _ _ s)    = findInstPath True s
findInstPath _       (SDo _ _ s _)       = findInstPath True s -- a do-loop performs at least one iteration
findInstPath _     s@(SWhile _ _ c _)    = if isInstExpr c then Just [Right c] else Nothing -- while and for-loops can terminate instantaneously
findInstPath _     s@(SFor _ _ _ _)      = Just [Left s]
findInstPath b       (SChoice _ _ ss)    = shortest $ catMaybes $ map (findInstPath b) ss
findInstPath _       (SPause _ _)        = Nothing
findInstPath _       (SWait _ _ _)       = Nothing
findInstPath _       (SStop _ _)         = Nothing
findInstPath True  s@(SBreak _ _)        = Just [Left s]
findInstPath False s@(SBreak _ _)        = Nothing
findInstPath b     s@(SInvoke _ _ m mas) = let (_,meth) = getMethod ?scope m
                                           in if elem (methCat meth) [Function,Procedure,Task Uncontrollable,Task Invisible] 
                                                 then if all isInstExpr $ catMaybes mas 
                                                         then Just [Left s]
                                                         else Nothing
                                                 else Nothing
findInstPath _     s@(SAssert _ _ _)     = Just [Left s]
findInstPath _     s@(SAssume _ _ _)     = Just [Left s]
findInstPath _     s@(SAssign _ _ _ r)   = if isInstExpr r then Just [Left s] else Nothing
findInstPath b     s@(SITE _ _ c t e)    = if not $ isInstExpr c 
                                              then Nothing
                                              else case e of 
                                                        Nothing -> Just [Right c]
                                                        Just st -> shortest $ catMaybes $ map (findInstPath b) $ [t,st]
findInstPath b     s@(SCase _ _ _ cs md) = shortest $ catMaybes $ map (findInstPath b) $ (map snd cs) ++ maybeToList md
findInstPath _       (SMagic _ _)        = Nothing


isBreak :: Either Statement Expr -> Bool
isBreak (Left (SBreak _ _)) = True
isBreak _                 = False

-- Return a path that ends with a break if one exists;
-- otherwise return the first path from the list of Nothing
-- if the list is empty
shortest :: [[Either Statement Expr]] -> Maybe [Either Statement Expr]
shortest [] = Nothing
shortest ps = case find (\p -> if' (null p) False (isBreak $ last p)) ps of
                   Nothing -> Just $ head ps
                   Just p  -> Just p
