module Spec2ASL() where

import qualified Data.Map             as M
import qualified Data.Graph.Inductive as G

import CFA
import ACFA
import Cascade

spec2ASL :: (?spec::Spec, ?pred::[Predicate]) => 
spec2ASL = 
    text "STATE"
    $+$
    (vcat $ map (<> semi) sdecls)
    $+$ 
    text "LABEL"
    $+$
    (vcat $ map (<> semi) ldecls)
    $+$
    text "INIT"
    $+$
    inits
    $+$
    text "GOAL"
    $+$
    goal
    $+$
    text "FAIR"
    $+$
    text "false"
    $+$
    text "CONT"
    $+$
    cont
    $+$
    text "TRANS"
    $+$
    (vcat $ map (<> semi) upds)
    where
    lscalars = map varScalars $ filter ((==VarTmp)   . varCat) $ specVar ?spec
    sscalars = map varScalars $ filter ((==VarState) . varCat) $ specVar ?spec
    ldecls   = map mkDecl lscalars
    sdecls   = map mkDecl sscalars
    upds     = map mkVarUpd sscalars
    inits    = (\(t, e) ->  mkExpr e <+> text "&&" <+> mkTranPrecondition t) $ tsInit $ specTrans ?spec
    goal     = head $ map (mkTranPrecondition . goalCond) $ tsGoal $ specTran ?spec
    constr   = autoConstr /\ preconditions
    cont     = mkExpr $ mkContVar === true

mkVarUpd :: (?spec::Spec) => Expr -> Doc
mkVarUpd e = mkExpr e <+> text ":=" <+> mkECascade upds
   where
   upds = CasTree $ (map (varUpd1 e) $ (tsUTran $ specTran ?spec) ++ (tsCTran $ specTran ?spec)) ++ 
                    [(FTrue, CasLeaf e)]


varUpd1 :: (?spec::Spec) => Expr -> Transition -> (Formula, ECascade)
varUpd1 e Transition{..} = if' (G.isEmpty cfa') Nothing
                           $ Just (acfa2asl (Just e) acfa, acfa2asl Nothing acfa)
    where av =   if' (isEnum e) (AVarEnum $ scalarExprToTerm e)
               $ if' (isBool e) (AVarBool $ scalarExprToTerm e)
               $ if' (isInt e)  (AVarInt  $ scalarExprToTerm e)
               $ error "varUpd1: not a scalar"
          cfa' = pruneCFAVar av tranCFA
          cfa  = cfaLocInlineWirePrefix ?spec cfa' tranFrom
          acfa = tranCFAToACFA [a]v tranFrom cfa

mkECascade :: (?spec::Spec) => ECascade -> Doc
mkECascade (CasLeaf e)  = mkExpr r
mkECascade (CasTree bs) = text "case" <+> braces $ nest 4 $ vcat $ 
                          map (\(f, cas) -> mkForm f <+> colon <+> mkECascade cas <+> semi) bs

mkForm :: (?spec::Spec) => Formula -> Doc
mkForm = mkExpr . formToExpr

mkExpr :: (?spec::Spec) => Expr -> Doc
mkExpr   (EVar n)          = mkName n
mkExpr   (EConst v)        = mkVal  v
mkExpr e@(EField _ _)      = mkName $ show e
mkExpr   (EUnOp Not e)     = parens $ char '!' <> mkExpr e
mkExpr   (EBinOp op e1 e2) = parens $ mkExpr e1 <+> mkBOp op <+> mkExpr e2
mkExpr   (ESlice e (l,h))  = mkExpr e <+> (brackets $ int l <+> colon <+> int h)
mkExpr   e                 = error $ "mkExpr" ++ show e

mkDecl :: (?spec::Spec) => Expr -> Doc
mkDecl e = mkExpr e <+> colon <+> 
           case typ e of
                UInt 1 -> text "conc" <+> text "uint<1>"
                UInt w -> text "abs " <+> text "uint<" <> int w <> char '>'
                Bool   -> text "conc" <+> text "bool"
                Enum n -> text "conc" <+> (braces $ hcat $ punctuate comma $ map mkName $ enumEnums $ getEnumeration n)

mkTranPrecondition :: (?spec::Spec) => Transition -> Doc
mkTranPrecondition Transition{..} = mkECascade $ acfa2asl Nothing acfa
    where acfa = tranCFAToACFA [] tranFrom tranCFA

-- Convert ACFA to variable update function in Adam's specification language.

acfa2asl :: (?spec::Spec) => Maybe Expr -> ACFA -> ECascade
acfa2asl me acfa = let ?acfa = acfa 
                       ?me    = me
                   in acfa2asl' init
    where init = fromJust $ find (null . G.pre acfa) $ G.nodes acfa


acfa2asl' :: (?spec::Spec,?acfa::ACFA,?me::Maybe Expr) => Loc -> ECascade
acfa2asl' l | (null $ G.suc ?acfa l)        = CasLeaf $ maybe true id ?me
            | (length (G.lsuc ?acfa l) > 1) = CasTree $ map (\(l', (_, Just pre,_)) -> (pre, acfa2asl' l'))
                                                      $ G.lsuc ?acfa l
            | otherwise                     = case head $ G.lsuc ?acfa l of
                                                   -- non-branching assume statements are taken into account in
                                                   -- the precondition of the entire state transition
                                                   (l', (_, Just pre, []))   -> maybe (CasTree [(pre, acfa2asl' l')]) (acfa2asl' l')  ?me
                                                   (l', (_, Nothing,  upds)) -> ecasSubst (acfa2asl' l') 
                                                                                $ zip (fst $ fromJust $ G.lab ?acfa l') upds


ecasSubst :: (?spec::Spec) => ECascade -> [(AbsVar, ECascade)] -> ECascade
ecasSubst ecas substs = foldl' ecasSubst1 ecas substs

ecasSubst1 :: (?spec::Spec) => ECascade -> (AbsVar, ECascade) -> ECascade
ecasSubst1 ecas (av, ecas') = casMap (ecasSubstAVar ecas av) ecas'

ecasSubstAVar :: (?spec::Spec) => ECascade -> AbsVar -> Expr -> ECascade
ecasSubstAVar (CasTree bs) av e'            = map (\(f,cas) -> (formSubstAVar av e' f, ecasSubstAVar cas av e')) bs
ecasSubstAVar (CasLeaf e) av e' | isBool e  = formSubstAVar av e' $ ptrFreeBExprToFormula e
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
formSubstAVar av e   (FEqConst av' i)            = ptrFreeBExprToFormula $ EBinOp Eq (if' (av' == av) e (avarToExpr av1)) $ EConst $ avarValToConst av i
formSubstAVar av e   (FBinOp op f1 f2)           = FBinOp op (formSubstAVar av e f1) (formSubstAVar av e f2)
formSubstAVar av e   (FNot f)                    = FNot $ formSubstAVar av e f
