{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module TSL2C.TSL2C() where

import Data.Maybe
import Data.List
import Data.Bits
import Language.C hiding (Pos, nopos)
import Language.C.Data.Ident

import Frontend.NS
import Frontend.Type
import Frontend.Template
import Frontend.TemplateOps
import Frontend.Method
import Frontend.TVar
import Frontend.Process
import Frontend.Expr
import Frontend.ExprOps
import Frontend.Statement
import Frontend.Const
import qualified Pos  as TSL
import qualified Name as TSL
import Pos
import Ops
import TSLUtil
import Util

-- Wrappers around Language.C constructors
cDecl :: CDeclSpec -> [(Maybe (CDeclarator a), Maybe (CInitializer a), Maybe (CExpression a))] -> CDecl
cDecl dspec decls = CDecl [dspec] decls undefNode

cDeclr :: Maybe Ident -> [CDerivedDeclr] -> CDeclr
cDeclr n ds = CDeclr n ds Nothing [] undefNode

cFunDeclr :: [CDecl] -> CDerivedDeclr
cFunDeclr as = CFunDeclr (Right ([as], False)) [] undefNode

cInitExpr :: CExpr -> CInit
cInitExpr e = CInitExpr e undefNode

cMemberDesig :: Ident -> CDesignator
cMemberDesig n = CMemberDesig n undefNode

cVoidType :: CTypeSpec
cVoidType = CVoidType undefNode

cBoolType :: CTypeSpec
cBoolType = CBoolType undefNode

cFunDef :: [CDeclSpec] -> CDeclr -> CStat -> CFunDef
cFunDef dspecs declr body = CFunDef dspecs declr [] body undefNode

cCompound :: [CBlockItem] -> CStat
cCompound is = CCompound is undefNode

cReturn :: Maybe CExpr -> CStat
cReturn e = CReturn e undefNode

cBreak :: CStat
cBreak = CBreak undefNode

cIf :: CExpr -> CStat -> Maybe CStat -> CStat
cIf i t me = CIf i t me undefNode

cSwitch :: CExpr -> CStat -> CStat
cSwitch x s = CSwitch x s undefNode

cCase :: CExpr -> CStat -> CStat
cCase x s = CCase x s undefNode

cWhile :: CExpr -> CStat -> Bool -> CStat
cWhile cond body dowhile = CWhile cond body dowhile undefNode

cVar :: String -> CExpr
cVar n = CVar (cident n) undefNode

cAssign :: CExpr -> CExpr -> CExpr
cAssign l r = CAssign CAssignOp l r undefNode

cExpr :: CExpr -> CStat
cExpr e = CExpr (Just e) undefNode

cUnary :: CUnaryOp -> CExpr-> CExpr
cUnary op e = CUnary op e undefNode

cBinary :: CBinaryOp -> CExpr -> CExpr -> CExpr
cBinary op e1 e2 = CBinary op e1 e2 undefNode

genBOp :: BOp -> CBinaryOp
genBOp Eq       = CEqOp
genBOp Neq      = CNeqOp
genBOp Lt       = CLeOp
genBOp Gt       = CGrOp
genBOp Lte      = CLeqOp
genBOp Gte      = CGeqOp
genBOp And      = CLndOp
genBOp Or       = CLorOp
genBOp BAnd     = CAndOp
genBOp BOr      = COrOp
genBOp BXor     = CXorOp
genBOp Plus     = CAddOp
genBOp BinMinus = CSubOp
genBOp Mod      = CRmdOp
genBOp Mul      = CMulOp

genUOp :: UOp -> CUnaryOp
genUOp Not    = CNegOp
genUOp UMinus = CMinOp
genUOp BNeg   = CCompOp
genUOp Deref  = CIndOp
genUOp AddrOf = CAdrOp

cCall :: CExpr -> [CExpr] -> CExpr
cCall f as = CCall f as undefNode

cCond :: CExpr -> CExpr -> CExpr -> CExpr
cCond i t e = CCall i (Just t) e undefNode

etrue :: CExpr
etrue = CConst $ cIntConst 1 DecRepr noFlags

cIntConst :: CInteger -> CConst
cIntConst i = CIntConst i undefNode

cStruct :: [CDecl] -> CStructUnion
cStruct ds = CStruct CStructTag Nothing (Just ds) [] undefNode

cCompoundLit :: CDecl -> [(CDesignator, CExpr)] -> CExpr
cCompoundLit d fs = CCompoundLit d $ map (\(desig, i) -> ([desig],i)) fs

cMember :: CExpr -> Ident -> Bool -> CExpr
cMember e f ptr = CMember e f ptr undefNode

cIndex :: CExpr -> CExpr -> CExpr
cIndex a i = Ident a i undefNode

cSUType :: CStructUnion -> CTypeSpec
cSUType cs = CSUType cs undefNode

cTypeDef :: Ident -> CTypeSpec
cTypeDef i = CTypeDef i undefNode

cTypedef :: CStorageSpec
cTypedef = CTypedef undefNode

cPtrDeclr :: [CTypeQual] -> CDerivedDeclr
cPtrDeclr qs = CPtrDeclr qs undefNode

cArrDeclr :: [CTypeQual] -> CArrSize -> CDerivedDeclr
cArrDeclr qs sz = CArrDeclr qs sz undefNode

cConstQual :: CTypeQual
cConstQual = CConstQual undefNode

cident :: String -> Ident
cident = builtinIdent 

cname :: (TSL.WithName a) => a -> Ident
cname = cident . TSL.sname

toCompound :: CStat -> CStat
toCompound s(CCompound _ _ _) = s
toCompound s                  = cCompound [CBlockStmt s]

this :: CExpr
this = cVar "this"

parentName :: TSL.Ident -> String
parentName n = "p" ++ TSL.sname n

constructorName :: (TSL.WithName a) => a -> String
constructorName t = "init_" ++ TSL.sname t 

genDecl :: (?scope::Scope) => [CDeclSpec] -> String -> TypeSpec -> Maybe CInit -> CDecl
genDecl cdeclspecs declname typespec initval = 
    cDecl (cdeclspecs++[cdeclspec]) [(cDeclr (Just $ cident declname) derdecls, initval, Nothing)]
    where (cdeclspec, derdecls) = genDecl' typespec

genDecl' :: (?scope::Scope) => TypeSpec -> (CDeclSpec, [CDerivedDeclr])
genDecl' (BoolSpec _)           = (CTypeSpec cBoolType, [])
genDecl' (SIntSpec p w)         = (CTypeSpec $ genInt p True w, [])
genDecl' (UIntSpec p w)         = (CTypeSpec $ genInt p False w, [])
genDecl' (StructSpec _ fs)      = (CTypeSpec $ genStruct fs, [])
genDecl' (EnumSpec _ es)        = (CTypeSpec $ genEnum es, [])
genDecl' (UserTypeSpec _ s)     = (CTypeSpec $ cTypeDef (cname $ last s), [])
genDecl' (PtrSpec _ t)          = (ctspec, (cPtrDeclr []):derdecls)
                                  where (ctspec, derdecls) = genDecl' t
genDecl' (ArraySpec _ t l)      = (ctspec, (cArrDeclr [] (CArrSize False $ genExpr l)):derdecls)
                                  where (ctspec, derdecls) = genDecl' t
genDecl' (VarArraySpec _ t l)   = (ctspec, cArrDeclr [] (CNoArrSize True)):derdecls
                                  where (ctspec, derdecls) = genDecl' t
genDecl' (TemplateTypeSpec _ n) = (CTypeSpec $ cTypeDef $ cident n, [])

genInt :: Pos -> Bool -> Int -> CTypeSpec
genInt p True  w | w <= 8    = cTypeDef $ cident "s8"
                 | w <= 16   = cTypeDef $ cident "s16"
                 | w <= 32   = cTypeDef $ cident "s32"
                 | w <= 64   = cTypeDef $ cident "s64"
                 | otherwise = err p "type too wide for C"
genInt p False w | w <= 8    = cTypeDef $ cident "u8"
                 | w <= 16   = cTypeDef $ cident "u16"
                 | w <= 32   = cTypeDef $ cident "u32"
                 | w <= 64   = cTypeDef $ cident "u64"
                 | otherwise = err p "type too wide for C"

genStruct :: [Field] -> CTypeSpec
genStruct fs = cSUType $ cStruct $ map (\f -> genDecl [] (TSL.sname f) (tspec f) Nothing) fs

genEnum :: [Enumerator] -> CTypeSpec
genEnum es = CEnumType (CEnum Nothing (Just $ map (\e -> (cname e, Nothing)) es) [] undefNode) undefNode

genType :: (?scope::Scope) => TypeDecl -> CDecl
genType d = genDecl [CStorageSpec cTypedef] (TSL.sname d) (tspec d) Nothing
  
genConst :: (?scope::Scope) => Const -> CDecl
genConst c = genDecl [CTypeQual cConstQual] (TSL.sname c) (tspec c) (Just $ cInitExpr $ genExpr $ constVal c)

genStat :: (?scope::Scope) => Statement -> CStat
genStat s = toStatement $ genStat' s

genStat' :: (?scope::Scope) => Statement -> [CBlockItem]
genStat' (SVarDecl _ _ v)         = [CBlockDecl $ genDecl [] (TSL.name v) (tspec v) (fmap (cInitExpr . genExpr) $ varInit v)]
genStat' (SReturn  _ _ me)        = [CBlockStmt $ cReturn $ fmap genExpr me]
genStat' (SSeq     _ _ ss)        = [CBlockStmt $ cCompound $ concatMap genStat' ss]
genStat' (SPar     p _ _)         = err p "cannot translate parallel block to C"
genStat' (SForever _ _ s)         = [CBlockStmt $ cWhile etrue (genStat s) False]
genStat' (SDo      _ _ s c)       = [CBlockStmt $ cWhile (genExpr c) (genStat s) True]
genStat' (SWhile   _ _ c s)       = [CBlockStmt $ cWhile (genExpr c) (genStat s) False]
genStat' (SFor     p _ (i,c,n) s) = err p "genStat SFor not implemented" 
genStat' (SChoice  p _ ss)        = err p "cannot transalte nondeterministic choice to C"
genStat' (SPause   _ _)           = []
genStat' (SWait    _ _ e)         = [CBlockStmt $ cExpr $ cCall (cVar "wait") [genExpr e]]
genStat' (SStop    _ _)           = []
genStat' (SBreak   _ _)           = [CBlockStmt cBreak]
genStat' (SInvoke  p _ ref as)    = [CBlockStmt $ cExpr $ genCall p ref as]
genStat' (SAssert  _ _ e)         = [CBlockStmt $ cCall (cVar "assert") [genExpr e]]
genStat' (SAssume  _ _ e)         = [CBlockStmt $ cCall (cVar "assume") [genExpr e]]
genStat' (SAssign  _ _ l r)       = [CBlockStmt $ cExpr $ cAssign (genExpr l) (genExpr r)]
genStat' (SITE     _ _ i t me)    = [CBlockStmt $ cIf (genExpr i) (genStat t) (fmap genStat me)]
genStat' (SCase    _ _ e cs md)   = [CBlockStmt $ cSwitch (genExpr e) $ cCompound $ map CBlockStmt $ cases++def]
                                    where cases = map (\(ex,st) -> cCase (genExpr ex) (toStatement $ genStat' st ++ [cBreak])) cs
                                          def   = maybe [] (return . genStat) md
genStat' (SMagic   p _)           = err p "cannot translate magic block to C"

toStatement :: [CBlockItem] -> CStat
toStatement [CBlockStmt s] = s
toStatement is             = cCompound is

genExpr :: (?scope::Scope) => Expr -> CExpr
genExpr (ETerm posit sym)      = 
    case getTerm ?scope sym of
         (ObjPort _ p)          -> cMember this (cname p) True
         (ObjInstance _ _)      -> err posit "genExpr: ObjInstance not implemented"
         (ObjVar  _ v)          -> cVar (TSL.sname v)
         (ObjGVar tm v)         -> genPath this (tmPathTo tm (name v)) (name v)
         (ObjWire _ _)          -> err posit "genExpr: ObjWire not implemented"
         (ObjArg _ a)           -> case argDir a of
                                        ArgIn  -> cVar (TSL.sname a)
                                        ArgOut -> cUnary CIndOp $ cVar (cname a)
         (ObjConst _ c)         -> cVar (TSL.sname c)
         (ObjEnum  _ e)         -> cVar (TSL.sname e)
genExpr (ELit  _ w s r v)    = CConst $ cIntConst $ CInteger v repr $ foldl' setFlag noFlags flags
                               where repr = case r of
                                                 Rad10 -> DecRepr
                                                 Rad16 -> HexRepr
                                                 Rad8  -> OctalRepr
                                                 Rad2  -> HexRepr
                                     flags = if' s [] [FlagUnsigned]
                                             ++
                                             if' (w > 32) [FlagLongLong] []
genExpr (EBool _ b)          = CConst $ cIntConst $ CInteger (if' b 1 0) DecRepr noFlags
genExpr (EApply p ref as)    = genCall p ref as
genExpr e@(EField _ e' f)    = case (exprTypeSpec e', exprTypeSpec e) of
                                    (TemplateTypeSpec _ _, TemplateTypeSpec _ _) -> cMember (genExpr e') (cident f) True
                                    (TemplateTypeSpec _ tname, _)                -> genPath (genExpr e') (tmPathTo (getTemplate tname) f) f
                                    _                                            -> cMember (genExpr e') (cident f) False
genExpr (EPField _ e f)      = cMember (genExpr e) (cident f) True
genExpr (EIndex  _ a i)      = cIndex  (genExpr a) (genExpr i)
genExpr (ERange  p _ _)      = err p "cannot translate array sub-range expression to C"
genExpr (ELength p _)        = err p "cannot translate array length expression to C"
genExpr (EUnOp   _ op e)     = cUnary (genUOp op) (genExpr e) 
genExpr (EBinOp _ Imp e1 e2) = cBinary CLorOp (cUnary CNegOp $ genExpr e1) (genExpr e2)
genExpr (EBinOp _ BConcat e1 e2) = genConcat e1 e2
genExpr (EBinOp _ op e1 e2)  = cBinary (genBOp op) (genExpr e1) (genExpr e2)
genExpr (ETernOp _ e1 e2 e3) = cCond (genExpr e1) (Just $ genExpr e2) (genExpr e3)
genExpr (ECase p _ _ _)      = err p "genExpr: ECase not implemented"
genExpr (ECond p _ _)        = err p "genExpr: ECond not implemented"
genExpr (ESlice  _ e (l,h))  = masked
                               where e' = genExpr e
                                     mask = CConst $ cIntConst (complement $ (-1) `shiftL` (h-l+1)) HexRepr noFlags
                                     shifted = if' (l==0) e' (cBinary CShrOp e' (CConst $ cIntConst l DecRepr noFlags))
                                     masked  = if' (h==exprWidth e - 1) shifted (cBinary CAndOp shifted mask)
genExpr (EStruct _ tname fs) = cCompoundLit (cDecl [CTypeSpec $ cTypedef $ last tname] []) fs'
                               where fs' = case fs of
                                                Left es  -> map (\(f,e) -> (cMemberDesig $ cident f, cInitExpr $ genExpr e)) es
                                                Right es -> map (\e -> ([], cInitExpr $ genExpr e)) es 
genExpr (EAtLab p _)         = err p "cannot convert @-expression to C"
genExpr (ENonDet p _)        = err p "cannot conver non-deterministic value to C"

genConcat :: (?scope::Scope) => Expr -> Expr -> Expr
genConcat e1 e2 = cBinary COrOp (genExpr e1) (cBinary CShlOp e2 $ CConst $ cIntConst (exprWidth e1) DecRepr noFlags)

genCall :: (?scope::Scope) => Pos -> MethodRef -> [Expr] -> CExpr
genCall p ref as = cExpr $ cCall mexpr (tmexpr:mapIdx (\ma i -> maybe (err p "missing argument in method call") (genArgExpr i) ma) as)
    where (mexpr,tmexpr) = genMRef ref
          meth = getMethod ?scope ref
          genArgExpr :: Int -> Expr -> CExpr
          genArgExpr i a = if (argDir $ methArg meth !! i) == ArgIn
                              then genExpr a
                              else cUnary CAdrOp $ genExpr a

-- Return path to method and expression to use as the first argument
-- If local method and imlemented in this template, call it directly with (this)
-- otherwise, generate path to the right instance, then generate path to parent template
genMRef :: (?scope::Scope) => MethodRef -> (CExpr, CExpr)
genMRef ref@(MethodRef _ path) =
    if (null $ init path) && (null $ tmPathTo tm $ head path) && (not $ methIsVirtual m)
       then (cVar $ cname m, this)
       else (cMember parpath (cname m) ptr, if' ptr parpath (cUnary CAdrOp parpath))
    where (tm', m) = getMethod ref
          tm = scopeTm ?scope
          instpath = foldl' (\e n -> cMember e (cident n) True) this path
          (parpath, ptr) = foldl' (\(e,isptr) n -> (cMember e (cident $ parentName n) isptr, False)) (instpath True) $ tmPathTo tm' (TSL.name m)

genPath :: CExpr -> [TSL.Ident] -> TSL.Ident -> CExpr
genPath e p x = cMember (foldl' (\e n -> cMember e (cname n) False) e p) (cname x) True

genMeth :: (?scope::Scope) => Method -> CFunDef
genMeth m@Method{..} = cFunDef [cdeclspec] (cDeclr (Just $ cname m) (args:derdecls), Nothing, Nothing) body
    where ScopeTemplate tm = ?scope
          -- is function declared in a parent template?
          path = tmPathTo tm $ TSL.name m
          isDerived = null path
          declaredIn = if' isDerived (getTemplate $ last path) tm
          pdeclaredIn = "p" ++ TSL.sname declaredIn
          pathToContainer :: Template -> [TSL.Ident] -> CExpr
          pathToContainer _ [] = cVar $ TSL.sname pdeclaredIn
          pathToContainer t p  = cCall (cVar "container_of") [pathToContainer (getTemplate [head p]) (tail p), cVar $ parentName $ TSL.name t, cVar $ TSL.sname $ head p]
          (cdeclspec, derdecls) = maybe (CTypeSpec cVoidType, []) genDecl' methRettyp
          args = cFunDeclr $ (genDecl [] (if' isDerived pdeclaredIn "this") (PtrSpec nopos $ TemplateTypeSpec nopos $ TSL.name declaredIn) Nothing) :
                             map (\a -> genDecl [] (TSL.sname a) (if' (argDir a == ArgIn) (tspec a) (PtrSpec nopos (tspec a))) Nothing) methArg
          asnthis = if isDerived
                       then []
                       else [CBlockDecl $ genDecl [] "this" (PtrSpec nopos $ TemplateTypeSpec nopos $ TSL.name tm) (Just $ pathToContainer tm path)]
          body = let sc = ?scope in
                 let ?scope = ScopeMethod tm m in 
                 case methBody of
                      Left _  -> err (TSL.pos m) "cannot generate definition of a virtual method"
                      Right s -> case genStat s of
                                      CCompound _ items _ -> cCompound (asnthis++items)
                                      s'                  -> cCompound (asnthis++[CBlockStmt s'])

genMethDecl :: (?scope::Scope) => Method -> CDecl
genMethDecl m = CDecl dspecs [(Just declr, Nothing, Nothing)] undefNode
    where CFunDef dspecs declr _ _= genMeth m

genProc :: (?scope::Scope) => Process -> CFunDef
genProc p = cFunDef [CTypeSpec cVoidType] 
                    (cDeclr (Just $ cname p) [cFunDeclr []], Nothing, Nothing) 
                    toCompound body
    where body = let ScopeTemplate tm = ?scope in
                 let ?scope = ScopeProcess tm p in
                 genStat $ procStatement p

genTemplate :: (?scope::Scope) => Template -> CTranslUnit
genTemplate t@Template{..} = CTranslUnit (types ++ consts ++ [struct] ++ prototypes ++ methods ++ processes ++ [constructor]) undefNode
   where -- collect all methods declared in the current template and its parents
         struct = let derived = map (\d -> genDecl [] (parentName $ drvTemplate d) (TemplateTypeSpec nopos $ drvTemplate d) Nothing) tmDerive
                      ports   = map (\p -> genDecl [] (TSL.sname p) (PtrSpec nopos $ TemplateTypeSpec nopos $ portTemplate p) Nothing) tmPort 
                      vars    = map (\v -> genDecl [] (TSL.sname v) (tspec v) Nothing) tmVar
                      -- only method declared in the local template
                      mdecls  = map (\m -> let CDecl dspecs [(Just (CDeclr n der Nothing [] _), mi, me)] _ = genMethDecl m
                                           in cDecl dspecs [(Just (cDeclr n (CPtrDeclr []:der)), mi, me)] n) 
                                $ filter (null . tmPathTo t . TSL.name) tmMethod
                      fields  = derived ++ ports ++ vars ++ mdecls
                  in CDeclExt $ cDecl [CStorageSpec cTypedef, 
                                       CTypeSpec $ cSUType $ cStruct fields]
                                      [(Just $ cDeclr (Just $ cname t) [], Nothing, Nothing)]
         constructor = let -- constructor initialises template variables and ports and calls parent constructors
                            args = (genDecl [] "this" (PtrSpec nopos $ TemplateTypeSpec nopos $ TSL.name t) Nothing) : 
                                   map (\p -> genDecl [] (TSL.sname p) (PtrSpec nopos $ TemplateTypeSpec nopos $ portTemplate p) Nothing) tmPort
                            -- bind local ports
                            portinit = map (\p -> cExpr $ cAssign (CMember this (cname p) True) (cVar $ TSL.sname p)) tmPort
                            -- call immediate parent constructors with correct ports
                            parentinit = map (\d -> let par = getTemplate $ drvTemplate d in
                                                    cExpr $ cCall (cVar $ constructorName par) 
                                                                  ((cUnary CAdrOp $ CMember this (cident $ parentName $ TSL.name par) True) : map (cVar . TSL.sname) $ tmPort par))
                                             tmDerive
                            -- initialise variables in this template only
                            varinit  = map (\v -> cExpr $ cAssign (CMember this (cname v) True) (genExpr $ fromJust $ varInit $ gvarVar v))
                                       $ filter (isJust . varInit . gvarVar) tmVar 
                            -- initialise local and all derived methods implemented here
                            methodinit = map (\m -> cExpr $ cAssign (genPath this (tmPathTo t $ TSL.name m) (TSL.name m)) (cVar $ TSL.sname m))
                                         $ filter (not . methIsVirtual) tmMethod
                            body = cCompound $ map CBlockStmt $ portinit ++ parentinit ++ varinit ++ methodinit
                       in CFDefExt $ cFunDef [CTypeSpec cVoidType] (cDeclr (Just $ cident $ constructorName t) [cFunDeclr args]) body
         -- types
         types = map (CDeclExt . genType) tmTypeDecl
         consts = map (CDeclExt . genConst) tmConst
         (prototypes, methods) = unzip $ map (\m -> (CDeclExt $ genMethDecl m, CFDefExt $ genMeth m)) $ filter (not . methIsVirtual) tmMethod
         processes = map (CFDefExt . genProc) tmProcess
         -- refuse to handle: init's, prefix, instance
