{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module Spec2ASL(spec2ASL) where

import qualified Data.Graph.Inductive as G
import Text.PrettyPrint
import Data.Maybe
import Data.List
import qualified Data.Map as M
import Debug.Trace

import Util hiding (trace)
import TSLUtil
import Ops 

import Inline
import ISpec
import IExpr
import IVar
import IType
import TranSpec
import CFA

import BFormula
import Predicate
import ACFA
import Cascade
import TSLAbsGame
import CFA2ACFA

spec2ASL :: Spec -> Doc
spec2ASL spec = 
    let ?spec = spec in
    let lscalars = concatMap ((\e -> exprScalars e (typ e)) . EVar . varName) $ filter ((==VarTmp)   . varCat) $ specVar ?spec
        sscalars = concatMap ((\e -> exprScalars e (typ e)) . EVar . varName) $ filter ((==VarState) . varCat) $ specVar ?spec
        ldecls   = map mkDecl lscalars
        sdecls   = map mkDecl sscalars
        upds     = map mkVarUpd sscalars
        initcond = (\(t, e) -> (mkForm $ ptrFreeBExprToFormula e) <+> text "&&" <+> mkTranPrecondition t "init") $ tsInit $ specTran ?spec
        goal     = head $ mapIdx (\g i -> mkTranPrecondition (goalCond g) ("goal" ++ show i)) $ tsGoal $ specTran ?spec
        fairs    = vcat $ map (\f -> (mkForm $ ptrFreeBExprToFormula $ fairCond f) <> semi) $ tsFair $ specTran ?spec
        constr   = mkForm autoConstr $+$ text "&&" $+$ mkAllPreconditions
        cont     = mkExpr $ mkContLVar === true in
    text "STATE"
    $+$
    (vcat $ map (<> semi) sdecls)
    $+$ text "" $+$ 
    text "LABEL"
    $+$
    (vcat $ map (<> semi) ldecls)
    $+$ text "" $+$
    text "OUTCOME"
    $+$ text "" $+$
    text "INIT"
    $+$
    initcond
    $+$ text "" $+$
    text "GOAL"
    $+$
    goal
    $+$ text "" $+$
    text "FAIR"
    $+$
    fairs
    $+$ text "" $+$
    text "CONT"
    $+$
    cont
    $+$ text "" $+$
    text "LABELCONSTRAINTS"
    $+$
    constr
    $+$ text "" $+$
    text "TRANS"
    $+$
    (vcat $ map (($+$ text "") . (<> semi)) upds)

mkAllPreconditions :: (?spec::Spec) => Doc
mkAllPreconditions = parens $ vcat $ punctuate (text "||")
                     $ (mkForm $ ptrFreeBExprToFormula $ mkTagVar /== (EConst $ EnumVal mkTagNone)) :
                       (mapIdx (\t i -> mkTranPrecondition t (show i)) $ (tsUTran $ specTran ?spec)) -- ++ (tsCTran $ specTran ?spec)


mkVarUpd :: (?spec::Spec) => Expr -> Doc
mkVarUpd e = {-trace("mkVarUpd =" ++ show e ++ "\n" ++ show upds) $ -} mkECascade (Just e) upds
   where
   upds | M.member (show e) (specUpds ?spec) = casTree 
                                               $ map (\(c,x) -> (ptrFreeBExprToFormula c, if typ x == Bool
                                                                                             then casTree [(ptrFreeBExprToFormula x, CasLeaf true), (FTrue, CasLeaf false)]
                                                                                             else CasLeaf x)) 
                                               $ (specUpds ?spec) M.! (show e)
        | otherwise = casTree $ (mapMaybe (varUpd1 e) $ (tsUTran $ specTran ?spec) ++ (tsCTran $ specTran ?spec)) ++ 
                                [(FTrue, CasLeaf e)]

varUpd1 :: (?spec::Spec) => Expr -> Transition -> Maybe (Formula, ECascade)
varUpd1 e Transition{..} = if' (G.isEmpty cfa') Nothing
                           $ Just (fcasToFormula $ fmap ptrFreeBExprToFormula $ acfa2ECas Nothing acfa, acfa2ECas (Just e) acfa)
    where av =   if' (isEnum e) (AVarEnum $ scalarExprToTerm e)
               $ if' (isBool e) (AVarBool $ scalarExprToTerm e)
               $ if' (isInt e)  (AVarInt  $ scalarExprToTerm e)
               $ error "varUpd1: not a scalar"
          cfa' = let ?pred=[] in pruneCFAVar [av] tranCFA
          cfa  = cfaLocInlineWirePrefix ?spec cfa' tranFrom
          acfa = let ?pred = [] in tranCFAToACFA [av] tranFrom cfa

mkECascade :: (?spec::Spec) => Maybe Expr -> ECascade -> Doc
mkECascade mlhs (CasLeaf e)  = maybe empty (\lhs -> mkExpr lhs <+> text ":=") mlhs <+> mkExpr e
mkECascade mlhs (CasTree bs) = (maybe empty (\lhs -> mkExpr lhs <+> text ":=") mlhs <+> text "case" <+> lbrace) 
                               $+$ (nest 4 $ vcat $ map (\(f, cas) -> case cas of 
                                                                           CasLeaf _ -> mkForm f <+> colon <+> mkECascade Nothing cas <+> semi
                                                                           CasTree _ -> mkForm f <+> colon $+$ (nest 4 $ mkECascade Nothing cas <+> semi)) bs) 
                               $+$ rbrace

mkForm :: (?spec::Spec) => Formula -> Doc
mkForm FTrue                    = text "true"
mkForm FFalse                   = text "false"
mkForm (FBoolAVar (AVarBool t)) = parens $ (mkExpr $ termToExpr t) <+> text "==" <+> text "1"
mkForm (FBinOp Impl  f1 f2)     = mkForm $ fdisj [fnot f1, f2]
mkForm (FBinOp Equiv f FTrue)   = mkForm f
mkForm (FBinOp Equiv f FFalse)  = mkForm $ fnot f
mkForm (FBinOp op f1 f2)        = parens $ (mkForm f1) <+> (mkBOp $ boolOpToBOp op) <+> (mkForm f2)
mkForm (FNot f)                 = parens $ char '!' <> mkForm f
mkForm f                        = mkExpr $ formToExpr f

mkExpr :: (?spec::Spec) => Expr -> Doc
mkExpr   (EVar n)           = mkName n
mkExpr   (EConst v)         = mkVal  v
mkExpr e@(EField _ _)       = mkName $ show e
mkExpr   (EUnOp Not e)      = parens $ char '!' <> mkExpr e
mkExpr   (EBinOp Imp e1 e2) = mkExpr $ EBinOp Or (EUnOp Not e1) e2
mkExpr   (EBinOp op  e1 e2) = parens $ mkExpr e1 <+> mkBOp op <+> mkExpr e2
mkExpr   (ESlice e (l,h))   = mkExpr e <+> (brackets $ int l <+> colon <+> int h)
mkExpr   e                  = error $ "mkExpr" ++ show e

mkBOp :: BOp -> Doc
mkBOp Eq  = text "=="
mkBOp Neq = text "!="
mkBOp And = text "&&"
mkBOp Or  = text "||"
mkBOp op  = error $ "mkBOp " ++ show op

mkDecl :: (?spec::Spec) => Expr -> Doc
mkDecl e = mkExpr e <+> colon <+> 
           case typ e of
                UInt 1 -> text "conc" <+> text "uint<1>"
                UInt w -> text "abs " <+> text "uint<" <> int w <> char '>'
                Bool   -> text "conc" <+> text "bool"
                Enum n -> text "conc" <+> (braces $ hcat $ punctuate comma $ map mkName $ enumEnums $ getEnumeration n)
                t      -> error $ "mkDecl " ++ show t

mkTranPrecondition :: (?spec::Spec) => Transition -> String -> Doc
mkTranPrecondition Transition{..} n = acfaTraceFile acfa ("pre" ++ n)
                                      $ mkForm $ fcasToFormula $ fmap ptrFreeBExprToFormula $ acfa2ECas Nothing acfa
    where acfa = let ?pred = [] in tranCFAToACFA [] tranFrom tranCFA

mkName :: String -> Doc
mkName = text . sanitize

mkVal :: Val -> Doc
mkVal (BoolVal True)  = int 1
mkVal (BoolVal False) = int 0
mkVal (UIntVal _ i)   = int $ fromInteger i
mkVal (EnumVal n)     = mkName n

-- Convert ACFA to variable update function in Adam's specification language.

acfa2ECas :: (?spec::Spec) => Maybe Expr -> ACFA -> ECascade
acfa2ECas me acfa = let ?acfa = acfa 
                        ?me    = me
                    in acfa2ECas' initloc
    where initloc = fromJust $ find (null . G.pre acfa) $ G.nodes acfa


acfa2ECas' :: (?spec::Spec,?acfa::ACFA,?me::Maybe Expr) => Loc -> ECascade
acfa2ECas' l | (null $ G.suc ?acfa l)        = CasLeaf $ maybe true id ?me
             | (length (G.lsuc ?acfa l) > 1) = casTree $ map (\(l', (_, Just pre,_)) -> (pre, acfa2ECas' l'))
                                                       $ G.lsuc ?acfa l
             | otherwise                     = let [(l', (_, mpre, upds))] = G.lsuc ?acfa l
                                                   ecas' = ecasSubst (acfa2ECas' l') 
                                                           $ zip (fst $ fromJust $ G.lab ?acfa l') upds
                                               -- non-branching assume statements are taken into account in
                                               -- the precondition of the entire state transition
                                               in maybe ecas' (\pre -> maybe (casTree [(pre, ecas')]) (\_ -> ecas') ?me) mpre


ecasSubst :: (?spec::Spec) => ECascade -> [(AbsVar, ECascade)] -> ECascade
ecasSubst ecas substs = foldl' ecasSubst1 ecas substs

ecasSubst1 :: (?spec::Spec) => ECascade -> (AbsVar, ECascade) -> ECascade
ecasSubst1 ecas (av, ecas') = casMap (ecasSubstAVar ecas av) ecas'

ecasSubstAVar :: (?spec::Spec) => ECascade -> AbsVar -> Expr -> ECascade
ecasSubstAVar (CasTree bs) av e'            = casTree $ map (\(f,cas) -> (formSubstAVar av e' f, ecasSubstAVar cas av e')) bs
ecasSubstAVar (CasLeaf e) av e' | isBool e  = CasLeaf $ formToExpr $ formSubstAVar av e' $ ptrFreeBExprToFormula e
                                | otherwise = CasLeaf $
                                              case scalarExprToTerm e of 
                                                   (TEnum _)   -> e
                                                   (TUInt _ _) -> e
                                                   (TSInt _ _) -> e
                                                   t           -> if' (isInt t && AVarInt t == av) e' $
                                                                  if' (av == AVarEnum t) e' e

formSubstAVar :: (?spec::Spec) => AbsVar -> Expr -> Formula -> Formula
formSubstAVar _  _   FTrue                       = FTrue
formSubstAVar _  _   FFalse                      = FFalse
formSubstAVar av e f@(FBoolAVar av') | av == av' = ptrFreeBExprToFormula e
                                     | otherwise = f
formSubstAVar av e   (FEq av1 av2)               = ptrFreeBExprToFormula $ EBinOp Eq (if' (av1 == av) e (avarToExpr av1)) (if' (av2 == av) e (avarToExpr av2))
formSubstAVar av e   (FEqConst av' i)            = ptrFreeBExprToFormula $ EBinOp Eq (if' (av' == av) e (avarToExpr av')) $ EConst $ avarValToConst av' i
formSubstAVar av e   (FBinOp op f1 f2)           = fbinop op (formSubstAVar av e f1) (formSubstAVar av e f2)
formSubstAVar av e   (FNot f)                    = fnot $ formSubstAVar av e f
