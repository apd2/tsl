{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module TSL2C.TSL2C(module2C) where

import Data.Maybe
import Data.List
import Data.Bits
import Text.PrettyPrint
import Language.C hiding (Pos, nopos)
import Language.C.Data.Ident
import System.FilePath.Posix

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
import Frontend.Spec
import Frontend.Grammar
import qualified Pos  as TSL
import qualified Name as TSL
import Pos
import Ops
import TSLUtil hiding (err)
import Util

-- TODO: use error monad
err p m = error $ spos p ++ ": " ++ m

module2C :: (?spec::Spec) => Bool -> [SpecItem] -> Doc
module2C h items = incls $$ text "" $$ (pretty $ CTranslUnit decls undefNode)
    where 
    (incls,decls) = foldl' (\(is, ds) i -> 
                             case i of 
                                  SpImport (Import _ n) -> (is $$ (text $ "#include <" ++ (dropExtensions $ TSL.sname n) ++ ".h>"), ds)
                                  SpType   decl         -> let ?scope = ScopeTop in (is, ds ++ (if' h [CDeclExt $ genType decl] []))
                                  SpConst  const        -> let ?scope = ScopeTop in (is, ds ++ (if' h [] [CDeclExt $ genConst const]))
                                  SpTemplate tm         -> let ?scope = ScopeTemplate tm in (is, ds ++ genTemplate tm h))
                           (empty, []) items

specItem2C :: (?spec::Spec) => Bool -> SpecItem -> Doc
specItem2C _ (SpImport (Import _ n)) = text $ "#include <" ++ (dropExtensions $ TSL.sname n) ++ ".h>"
specItem2C _ (SpType   decl)         = let ?scope = ScopeTop in pretty $ genType decl
specItem2C _ (SpConst  const)        = let ?scope = ScopeTop in pretty $ genConst const
specItem2C h (SpTemplate tm)         = let ?scope = ScopeTemplate tm in vcat $ map (($$ text "") . pretty) $ genTemplate tm h

-- Wrappers around Language.C constructors
cDecl :: [CDeclSpec] -> [(Maybe CDeclr, Maybe CInit, Maybe CExpr)] -> CDecl
cDecl dspecs decls = CDecl dspecs decls undefNode

cDeclr :: Maybe Ident -> [CDerivedDeclr] -> CDeclr
cDeclr n ds = CDeclr n ds Nothing [] undefNode

cFunDeclr :: [CDecl] -> CDerivedDeclr
cFunDeclr as = CFunDeclr (Right (as, False)) [] undefNode

cInitExpr :: CExpr -> CInit
cInitExpr e = CInitExpr e undefNode

cMemberDesig :: Ident -> CDesignator
cMemberDesig n = CMemberDesig n undefNode

cVoidType :: CTypeSpec
cVoidType = CVoidType undefNode

cIntType :: CTypeSpec
cIntType = CIntType undefNode

cFunDef :: [CDeclSpec] -> CDeclr -> CStat -> CFunDef
cFunDef dspecs declr body = CFunDef dspecs declr [] body undefNode

cCompound :: [CBlockItem] -> CStat
cCompound is = CCompound [] is undefNode

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

cOrAssign :: CExpr -> CExpr -> CExpr
cOrAssign l r = CAssign COrAssOp l r undefNode

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
cCond i t e = CCond i (Just t) e undefNode

etrue :: CExpr
etrue = CConst $ cIntConst 1 DecRepr noFlags

cIntConst :: Integer -> CIntRepr -> Flags CIntFlag -> CConst
cIntConst i r f = CIntConst (CInteger i r f) undefNode

cStruct :: Maybe Ident -> Maybe [CDecl] -> CStructUnion
cStruct mname ds = CStruct CStructTag mname ds [] undefNode

cCompoundLit :: CDecl -> [([CDesignator], CExpr)] -> CExpr
cCompoundLit d fs = CCompoundLit d (map (\(desig, i) -> (desig, cInitExpr i)) fs) undefNode

cMember :: CExpr -> Ident -> Bool -> CExpr
cMember e f ptr = CMember e f ptr undefNode

cIndex :: CExpr -> CExpr -> CExpr
cIndex a i = CIndex a i undefNode

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

cint :: Integer -> CExpr
cint i = CConst $ cIntConst i DecRepr noFlags

toCompound :: CStat -> CStat
toCompound s@(CCompound _ _ _) = s
toCompound s                   = cCompound [CBlockStmt s]

this :: CExpr
this = cVar "this"

parentName :: TSL.Ident -> String
parentName n = TSL.sname n

constructorName :: (TSL.WithName a) => a -> String
constructorName t = "init_" ++ TSL.sname t 

genDecl :: (?spec::Spec, ?scope::Scope) => [CDeclSpec] -> String -> TypeSpec -> Maybe CInit -> CDecl
genDecl cdeclspecs declname typespec initval = 
    cDecl (cdeclspecs++[cdeclspec]) [(Just $ cDeclr (Just $ cident declname) derdecls, initval, Nothing)]
    where (cdeclspec, derdecls) = genDecl' typespec

genDecl' :: (?spec::Spec, ?scope::Scope) => TypeSpec -> (CDeclSpec, [CDerivedDeclr])
genDecl' (BoolSpec _)           = (CTypeSpec cIntType, [])
genDecl' (SIntSpec p w)         = (CTypeSpec $ genInt p True w, [])
genDecl' (UIntSpec p w)         = (CTypeSpec $ genInt p False w, [])
genDecl' (StructSpec _ fs)      = (CTypeSpec $ genStruct fs, [])
genDecl' (EnumSpec _ es)        = (CTypeSpec $ genEnum es, [])
genDecl' (UserTypeSpec _ s)     = (CTypeSpec $ cTypeDef (cname $ last s), [])
genDecl' (PtrSpec _ t)          = (ctspec, (cPtrDeclr []):derdecls)
                                  where (ctspec, derdecls) = genDecl' t
genDecl' (ArraySpec _ t l)      = (ctspec, (cArrDeclr [] (CArrSize False $ genExpr l)):derdecls)
                                  where (ctspec, derdecls) = genDecl' t
genDecl' (VarArraySpec _ t)     = (ctspec, cArrDeclr [] (CNoArrSize True):derdecls)
                                  where (ctspec, derdecls) = genDecl' t
genDecl' (TemplateTypeSpec _ n) = (CTypeSpec $ cSUType $ cStruct (Just $ cname n) Nothing, [])

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

genStruct ::  (?spec::Spec, ?scope::Scope) => [Field] -> CTypeSpec
genStruct fs = cSUType $ cStruct Nothing $ Just $ map (\f -> genDecl [] (TSL.sname f) (tspec f) Nothing) fs

genEnum :: [Enumerator] -> CTypeSpec
genEnum es = CEnumType (CEnum Nothing (Just $ map (\e -> (cname e, Nothing)) es) [] undefNode) undefNode

genType :: (?spec::Spec, ?scope::Scope) => TypeDecl -> CDecl
genType d = genDecl [CStorageSpec cTypedef] (TSL.sname d) (tspec d) Nothing
  
genConst :: (?spec::Spec, ?scope::Scope) => Const -> CDecl
genConst c = genDecl [CTypeQual cConstQual] (TSL.sname c) (tspec c) (Just $ cInitExpr $ genExpr $ constVal c)

genStat :: (?spec::Spec, ?scope::Scope) => Statement -> CStat
genStat s = toStatement $ genStat' s

genStat' :: (?spec::Spec, ?scope::Scope) => Statement -> [CBlockItem]
genStat' (SVarDecl _ _ v)         = [CBlockDecl $ genDecl [] (TSL.sname v) (tspec v) (fmap (cInitExpr . genExpr) $ varInit v)]
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
genStat' (SAssert  _ _ e)         = [CBlockStmt $ cExpr $ cCall (cVar "assert") [genExpr e]]
genStat' (SAssume  _ _ e)         = [CBlockStmt $ cExpr $ cCall (cVar "assume") [genExpr e]]
genStat' (SAssign  _ _ l r)       = 
    case l of
         ESlice _ e (low, high)  -> let l' = fromInteger $ evalInt low
                                        h' = fromInteger $ evalInt high
                                        mask     = foldl' (\m i -> if' (i >= l' && i <= h') m (setBit m i)) (0::Integer) [0..exprWidth e - 1]
                                        maskexp  = CConst $ cIntConst mask HexRepr noFlags
                                        emasked  = cBinary CAndOp (genExpr e) maskexp
                                        shift    = cint $ fromIntegral l'
                                        rshifted = if' (l' == 0) (genExpr r) (cBinary CShlOp (genExpr r) shift) in
                                    [CBlockStmt $ cExpr $ cAssign (genExpr e) $ cBinary COrOp emasked rshifted]
         _                       -> [CBlockStmt $ cExpr $ cAssign (genExpr l) (genExpr r)]
genStat' (SITE     _ _ i t me)    = [CBlockStmt $ cIf (genExpr i) (genStat t) (fmap genStat me)]
genStat' (SCase    _ _ e cs md)   = [CBlockStmt $ cSwitch (genExpr e) $ cCompound $ map CBlockStmt $ cases++def]
                                    where cases = map (\(ex,st) -> cCase (genExpr ex) (toStatement $ genStat' st ++ [CBlockStmt cBreak])) cs
                                          def   = maybe [] (return . genStat) md
genStat' (SMagic   p _)           = err p "cannot translate magic block to C"

toStatement :: [CBlockItem] -> CStat
toStatement [CBlockStmt s] = s
toStatement is             = cCompound is

genExpr :: (?spec::Spec, ?scope::Scope) => Expr -> CExpr
genExpr (ETerm posit sym)      = 
    case getTerm ?scope sym of
         (ObjPort _ p)          -> cMember this (cname p) True
         (ObjInstance _ _)      -> err posit "genExpr: ObjInstance not implemented"
         (ObjVar  _ v)          -> cVar (TSL.sname v)
         (ObjGVar tm v)         -> genPath this (tmPathTo tm (TSL.name v)) (TSL.name v)
         (ObjWire _ _)          -> err posit "genExpr: ObjWire not implemented"
         (ObjArg _ a)           -> case argDir a of
                                        ArgIn  -> cVar (TSL.sname a)
                                        ArgOut -> cUnary CIndOp $ cVar (TSL.sname a)
         (ObjConst _ c)         -> cVar (TSL.sname c)
         (ObjEnum  _ e)         -> cVar (TSL.sname e)
genExpr (ELit  _ w s r v)    = CConst $ cIntConst v repr $ foldl' (flip setFlag) noFlags flags
                               where repr = case r of
                                                 Rad10 -> DecRepr
                                                 Rad16 -> HexRepr
                                                 Rad8  -> OctalRepr
                                                 Rad2  -> HexRepr
                                     flags = if' s [] [FlagUnsigned]
                                             ++
                                             if' (w > 32) [FlagLongLong] []
genExpr (EBool _ b)          = cint $ if' b 1 0
genExpr (EApply p ref as)    = genCall p ref as
genExpr e@(EField _ e' f)    = case (exprTypeSpec e', exprTypeSpec e) of
                                    (TemplateTypeSpec _ _, TemplateTypeSpec _ _) -> cMember (genExpr e') (cname f) True
                                    (TemplateTypeSpec _ tname, _)                -> genPath (genExpr e') (tmPathTo (getTemplate tname) f) f
                                    _                                            -> cMember (genExpr e') (cname f) False
genExpr (EPField _ e f)      = cMember (genExpr e) (cname f) True
genExpr (EIndex  _ a i)      = cIndex  (genExpr a) (genExpr i)
genExpr (ERange  p _ _)      = err p "cannot translate array sub-range expression to C"
genExpr (ELength p _)        = err p "cannot translate array length expression to C"
genExpr (EUnOp   _ op e)     = cUnary (genUOp op) (genExpr e) 
genExpr (EBinOp _ Imp e1 e2) = cBinary CLorOp (cUnary CNegOp $ genExpr e1) (genExpr e2)
genExpr (EBinOp _ BConcat e1 e2) = genConcat e1 e2
genExpr (EBinOp _ op e1 e2)  = cBinary (genBOp op) (genExpr e1) (genExpr e2)
genExpr (ETernOp _ e1 e2 e3) = cCond (genExpr e1) (genExpr e2) (genExpr e3)
genExpr (ECase p _ _ _)      = err p "genExpr: ECase not implemented"
genExpr (ECond p _ _)        = err p "genExpr: ECond not implemented"
genExpr (ESlice  _ e (l,h))  = masked
                               where e' = genExpr e
                                     mask = CConst $ cIntConst (complement $ (-1) `shiftL` (fromInteger $ evalInt h - evalInt l + 1)) HexRepr noFlags
                                     shifted = if' (evalInt l==0) e' (cBinary CShrOp e' (cint $ evalInt l))
                                     masked  = if' ((fromInteger $ evalInt h) == exprWidth e - 1) shifted (cBinary CAndOp shifted mask)
genExpr (EStruct _ tname fs) = cCompoundLit (cDecl [CTypeSpec $ cTypeDef $ cname $ last tname] []) fs'
                               where fs' = case fs of
                                                Left es  -> map (\(f,e) -> ([cMemberDesig $ cname f], genExpr e)) es
                                                Right es -> map (\e -> ([], genExpr e)) es 
genExpr (EAtLab p _)         = err p "cannot convert @-expression to C"
genExpr (ENonDet p _)        = err p "cannot conver non-deterministic value to C"

genConcat :: (?spec::Spec, ?scope::Scope) => Expr -> Expr -> CExpr
genConcat e1 e2 = cBinary COrOp (genExpr e1) (cBinary CShlOp (genExpr e2) $ cint $ fromIntegral $ exprWidth e1)

genCall :: (?spec::Spec, ?scope::Scope) => Pos -> MethodRef -> [Maybe Expr] -> CExpr
genCall p ref as = cCall mexpr (tmexpr:mapIdx (\ma i -> maybe (cVar "NULL") (genArgExpr i) ma) as)
    where (mexpr,tmexpr) = genMRef ref
          (_,meth) = getMethod ?scope ref
          genArgExpr :: Int -> Expr -> CExpr
          genArgExpr i a = if (argDir $ methArg meth !! i) == ArgIn
                              then genExpr a
                              else cUnary CAdrOp $ genExpr a

-- Return path to method and expression to use as the first argument
-- If local method and imlemented in this template, call it directly with (this)
-- otherwise, generate path to the right instance, then generate path to parent template
genMRef :: (?spec::Spec, ?scope::Scope) => MethodRef -> (CExpr, CExpr)
genMRef ref@(MethodRef _ path) =
    if (null $ init path) && (null $ tmPathTo tm $ head path) && (not $ methIsVirtual m)
       then (cVar $ TSL.sname m, this)
       else (cMember parpath (cname m) ptr, if' ptr parpath (cUnary CAdrOp parpath))
    where (tm', m) = getMethod ?scope ref
          tm = scopeTm ?scope
          instpath = foldl' (\e n -> cMember e (cname n) True) this (init path)
          (parpath, ptr) = foldl' (\(e,isptr) n -> (cMember e (cident $ parentName n) isptr, False)) (instpath, True) $ tmPathTo tm' (TSL.name m)

genPath :: CExpr -> [TSL.Ident] -> TSL.Ident -> CExpr
genPath e p x = fst $ foldl' (\(e,ptr) n -> (cMember e (cname n) ptr,False)) (e, True) (p++[x])

genMeth :: (?spec::Spec, ?scope::Scope) => Method -> CFunDef
genMeth m@Method{..} = cFunDef [cdeclspec] (cDeclr (Just $ cname m) (args:derdecls)) body
    where ScopeTemplate tm = ?scope
          -- is function declared in a parent template?
          path = tmPathTo tm $ TSL.name m
          isDerived = not $ null path
          declaredIn = if' isDerived (getTemplate $ last path) tm
          pdeclaredIn = "p" ++ TSL.sname declaredIn
          pathToContainer :: Template -> [TSL.Ident] -> CExpr
          pathToContainer _ [] = cVar pdeclaredIn
          pathToContainer t p  = cCall (cVar "container_of") [pathToContainer (getTemplate (head p)) (tail p), cVar $ parentName $ TSL.name t, cVar $ TSL.sname $ head p]
          (cdeclspec, derdecls) = maybe (CTypeSpec cVoidType, []) genDecl' methRettyp
          args = cFunDeclr $ (genDecl [] (if' isDerived pdeclaredIn "this") (PtrSpec nopos $ TemplateTypeSpec nopos $ TSL.name declaredIn) Nothing) :
                             map (\a -> genDecl [] (TSL.sname a) (if' (argDir a == ArgIn) (tspec a) (PtrSpec nopos (tspec a))) Nothing) methArg
          asnthis = if isDerived
                       then [CBlockDecl $ genDecl [] "this" (PtrSpec nopos $ TemplateTypeSpec nopos $ TSL.name tm) (Just $ cInitExpr $ pathToContainer tm path)]
                       else []
          body = let sc = ?scope in
                 let ?scope = ScopeMethod tm m in 
                 case methBody of
                      Left _  -> err (TSL.pos m) "cannot generate definition of a virtual method"
                      Right s -> case genStat s of
                                      CCompound _ items _ -> cCompound (asnthis++items)
                                      s'                  -> cCompound (asnthis++[CBlockStmt s'])

genMethDecl :: (?spec::Spec, ?scope::Scope) => Method -> CDecl
genMethDecl m = CDecl dspecs [(Just declr, Nothing, Nothing)] undefNode
    where CFunDef dspecs declr _ _ _ = genMeth m

genProc :: (?spec::Spec, ?scope::Scope) => Process -> CFunDef
genProc p = cFunDef [CTypeSpec cVoidType] 
                    (cDeclr (Just $ cname p) [cFunDeclr []]) 
                    (toCompound body)
    where body = let ScopeTemplate tm = ?scope in
                 let ?scope = ScopeProcess tm p in
                 genStat $ procStatement p

genTemplate :: (?spec::Spec, ?scope::Scope) => Template -> Bool -> [CExtDecl]
genTemplate t@Template{..} header = if header
                                       then types ++ consts ++ [struct] ++ [constructor]
                                       else prototypes ++ methods ++ processes ++ [constructor]
   where -- collect all methods declared in the current template and its parents
         struct = let derived = map (\d -> genDecl [] (parentName $ drvTemplate d) (TemplateTypeSpec nopos $ drvTemplate d) Nothing) tmDerive
                      ports   = map (\p -> genDecl [] (TSL.sname p) (PtrSpec nopos $ TemplateTypeSpec nopos $ portTemplate p) Nothing) tmPort 
                      vars    = map (\v -> genDecl [] (TSL.sname v) (tspec v) Nothing) tmVar
                      -- only methods declared in the local template
                      mdecls  = map (\m -> let CDecl dspecs [(Just (CDeclr n der Nothing [] _), mi, me)] _ = genMethDecl m
                                           in cDecl dspecs [(Just (cDeclr n (cPtrDeclr []:der)), mi, me)]) 
                                $ filter (null . tmPathTo t . TSL.name) tmMethod
                      fields  = derived ++ ports ++ vars ++ mdecls
                  in CDeclExt $ cDecl [CStorageSpec cTypedef, 
                                       CTypeSpec $ cSUType $ cStruct (Just $ cname t) (Just fields)]
                                      [(Just $ cDeclr (Just $ cname t) [], Nothing, Nothing)]
         constructor = let -- constructor initialises template variables and ports and calls parent constructors
                            args = (genDecl [] "this" (PtrSpec nopos $ TemplateTypeSpec nopos $ TSL.name t) Nothing) : 
                                   map (\p -> genDecl [] (TSL.sname p) (PtrSpec nopos $ TemplateTypeSpec nopos $ portTemplate p) Nothing) tmPort
                            -- bind local ports
                            portinit = map (\p -> cExpr $ cAssign (cMember this (cname p) True) (cVar $ TSL.sname p)) tmPort
                            -- call immediate parent constructors with correct ports
                            parentinit = map (\d -> let par@Template{tmPort=ports} = getTemplate $ drvTemplate d in
                                                    cExpr $ cCall (cVar $ constructorName par) 
                                                                  ((cUnary CAdrOp $ cMember this (cident $ parentName $ TSL.name par) True) : (map (cVar . TSL.sname) ports)))
                                             tmDerive
                            -- initialise variables in this template only
                            varinit  = map (\v -> cExpr $ cAssign (cMember this (cname v) True) (genExpr $ fromJust $ varInit $ gvarVar v))
                                       $ filter (isJust . varInit . gvarVar) tmVar 
                            -- initialise local and all derived methods implemented here
                            methodinit = map (\m -> cExpr $ cAssign (genPath this (tmPathTo t $ TSL.name m) (TSL.name m)) (cVar $ TSL.sname m))
                                         $ filter (not . methIsVirtual) tmMethod
                            body = cCompound $ map CBlockStmt $ portinit ++ parentinit ++ varinit ++ methodinit
                       in if header
                             then CDeclExt $ cDecl [CTypeSpec cVoidType] [(Just $ cDeclr (Just $ cident $ constructorName t) [cFunDeclr args], Nothing, Nothing)]
                             else CFDefExt $ cFunDef [CTypeSpec cVoidType] (cDeclr (Just $ cident $ constructorName t) [cFunDeclr args]) body
         -- types
         types = map (CDeclExt . genType) tmTypeDecl
         consts = map (CDeclExt . genConst) tmConst
         (prototypes, methods) = unzip $ map (\m -> (CDeclExt $ genMethDecl m, CFDefExt $ genMeth m)) $ filter (not . methIsVirtual) tmMethod
         processes = map (CFDefExt . genProc) tmProcess
         -- refuse to handle: init's, prefix, instance
