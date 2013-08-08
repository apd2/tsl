module Spec2ASL() where

import qualified Data.Map             as M
import qualified Data.Graph.Inductive as G

import CFA
import ACFA
import Cascade

-- Convert ACFA to variable update function in Adam's specification language.

acfa2asl :: (?spec::Spec) => AbsVar -> ACFA -> ECascade
acfa2asl av acfa = let ?acfa = acfa 
                       ?av   = av 
                   in acfa2asl' init
    where init = fromJust $ find (null . G.pre acfa) $ G.nodes acfa


acfa2asl' :: (?spec::Spec,?acfa::ACFA, ?av::AbsVar) => Loc -> ECascade
acfa2asl' l | (null $ G.suc ?acfa l)        = CasLeaf $ avarToExpr ?av
            | (length (G.lsuc ?acfa l) > 1) = CasTree $ map (\(l', (_, Just pre,_)) -> (pre, acfa2asl' l'))
                                                      $ G.lsuc ?acfa l
            | otherwise                     = case head $ G.lsuc ?acfa l of
                                                   -- non-branching assume statements are taken into account in
                                                   -- the precondition of the entire state transition
                                                   (l', (_, Just pre, []))   -> acfa2asl' l'  
                                                   (l', (_, Nothing,  upds)) -> ecasSubst (acfa2asl' l') 
                                                                                $ zip (fst $ fromJust $ G.lab ?acfa l') upds


ecasSubst :: ECascade -> [(AbsVar, ECascade)] -> ECascade
ecasSubst ecas substs = foldl' ecasSubst1 ecas substs

ecasSubst1 :: ECascade -> (AbsVar, ECascade) -> ECascade
ecasSubst1 ecas (av, ecas') = casMap (ecasSubstAVar ecas av) ecas'

ecasSubstAVar :: ECascade -> AbsVar -> Expr -> ECascade
ecasSubstAVar (CasTree bs) av e'            = map (\(f,cas) -> (formSubstAVar av e' f, ecasSubstAVar cas av e')) bs
ecasSubstAVar (CasLeaf e) av e' | isBool e  = formSubstAVar av e' $ ptrFreeBExprToFormula e
                                | otherwise = CasLeaf $
                                              case scalarExprToTerm e of 
                                                   (TEnum _)   -> e
                                                   (TUInt _ _) -> e
                                                   (TSInt _ _) -> e
                                                   t           -> if' (isInt t && AVarInt t == av) e' $
                                                                  if' (av == AVarEnum t) e' e

formSubstAVar :: AbsVar -> Expr -> Formula -> Formula
formSubstAVar _  _   FTrue                       = FTrue
formSubstAVar _  _   FFalse                      = FFalse
formSubstAVar av e f@(FBoolAVar av') | av == av' = ptrFreeBExprToFormula e
                                     | otherwise = f
formSubstAVar av e   (FEq av1 av2)               = ptrFreeBExprToFormula $ EBinOp Eq (if' (av1 == av) e (avarToExpr av1)) (if' (av2 == av) e (avarToExpr av2))
formSubstAVar av e   (FEqConst av' i)            = ptrFreeBExprToFormula $ EBinOp Eq (if' (av' == av) e (avarToExpr av1)) $ 
                                                                                     case typ e of
                                                                                          UInt w -> EConst $ UIntVal w i
                                                                                          SInt w -> EConst $ SIntVal w i
                                                                                          Enum n -> (enumEnums $ getEnumeration n) !! i
formSubstAVar av e   (FBinOp op f1 f2)           = FBinOp op (formSubstAVar av e f1) (formSubstAVar av e f2)
formSubstAVar av e   (FNot f)                    = FNot $ formSubstAVar av e f
