{-# LANGUAGE ImplicitParams, RecordWildCards, TemplateHaskell #-}

module CFG (Step(..),
            Branch(..),
            gen1Step,
            derefStep,
            ppStep) where

import Data.Tuple.Select
import qualified Data.Map          as M
import Control.Monad.Error
import Data.List
import qualified Text.PrettyPrint  as PP

import Resource
import Pos
import PP
import TSLUtil
import Util
import Name
import Interface
import TermiteGame
import BddRecord
import Predicate
import BFormula
import AbsSim
import CG
import CodeGen
import ISpec hiding (getVar)
import IType
import IVar
import Inline
import PID
import BVSMT
import InstTree
import Method
import Expr
import qualified NS                as F
import qualified Spec              as F
import qualified IExpr             as I
import qualified CuddExplicitDeref as C
import qualified BddUtil           as C

data Branch s u = BranchITE    (DDNode s u) (DDNode s u) (Branch s u)
                | BranchAction (DDNode s u) (DDNode s u)
                | BranchStuck  

-- A single synthesised step, consisting of a wait condition and
-- an if-then-else fork.
data Step s u = Step { stepWaitCond :: DDNode s u -- wait condition
                     , stepBranches :: Branch s u 
                     }

ppStep :: (MonadResource (DDNode s u) (ST s) t) => F.Spec -> F.Spec -> Spec -> PrID -> C.STDdManager s u -> F.Scope -> DB s u AbsVar AbsVar -> Step s u -> t (ST s) PP.Doc
ppStep inspec flatspec spec pid m sc pdb Step{..} = do
    let ?inspec   = inspec
        ?flatspec = flatspec
        ?spec     = spec
        ?pid      = pid
        ?m        = m
        ?sc       = sc
        ?db       = pdb
    wait <- if stepWaitCond == C.bone m
               then return PP.empty
               else do cond <- ppCond stepWaitCond
                       return $ PP.text "wait" PP.<> PP.parens cond PP.<> PP.char ';'
    bs <- ppBranch stepBranches
    return $ wait PP.$+$ (PP.vcat $ PP.punctuate PP.semi bs)

ppBranch :: (MonadResource (DDNode s u) (ST s) t, ?inspec::F.Spec, ?flatspec::F.Spec, ?spec::Spec, ?pid::PrID, ?sc::F.Scope, ?m::C.STDdManager s u, ?db::DB s u AbsVar AbsVar) 
         => Branch s u -> t (ST s) [PP.Doc]
ppBranch BranchStuck       = return $ [PP.text "/* stuck */"]
ppBranch (BranchITE i t e) = do
    cond <- ppCond i
    tact <- ppAction t
    ebr  <- ppBranch e
    return $ [mkITE cond tact ebr]
ppBranch (BranchAction _ a) = ppAction a

ppCond :: (MonadResource (DDNode s u) (ST s) t, ?inspec::F.Spec, ?spec::Spec, ?pid::PrID, ?sc::F.Scope, ?m::C.STDdManager s u, ?db::DB s u AbsVar AbsVar) => DDNode s u -> t (ST s) PP.Doc
ppCond c = (liftM $ exprToTSL2 ?inspec ?pid ?sc) $ mkCondition c

ppAction :: (MonadResource (DDNode s u) (ST s) t, ?inspec::F.Spec, ?flatspec::F.Spec, ?spec::Spec, ?pid::PrID, ?sc::F.Scope, ?m::C.STDdManager s u, ?db::DB s u AbsVar AbsVar) 
         => DDNode s u -> t (ST s) [PP.Doc]
ppAction lab = do
    asns <- mkLabel lab
    let lvars = nub $ map varName $ filter ((==VarTmp) . varCat) $ concatMap (avarVar . fst) asns
    let sol = bvSolve asns lvars
    case sol of
         [] -> return $ [PP.text $ "/* could not concretise label: " ++ show asns ++ " */"]
         _  -> return $ ppAction' sol

ppAction' :: (?inspec::F.Spec, ?flatspec::F.Spec, ?spec::Spec, ?pid::PrID, ?sc::F.Scope) => [(I.Expr, [(String, VarAsn)])] -> [PP.Doc]
ppAction' ((cond, lab):sol) = if null sol
                                 then act
                                 else [mkITE (exprToTSL2 ?inspec ?pid ?sc cond) act (ppAction' sol)]
    where
    flatspec = ?flatspec
    eact = do 
        -- extract tag
        tag <- case lookup mkTagVarName lab of
                    Just (AsnScalar [(_, Right (I.EConst (I.EnumVal tname)))]) -> return tname
                    _                                                          -> throwError $ "cannot extract tag from label assignment " ++ show lab
        -- generate method invocation
        if' (tag == mkTagDoNothing) (throwError "unexpected no-op tag") $
            if' (tag == mkTagExit) (return [PP.text "{}"]) $
            do let mpath = tagToPath tag 
                   -- method in the flat spec
                   meth  = let ?spec = flatspec in snd $ F.getMethod ?sc $ MethodRef nopos [Ident nopos tag]
                   args  = map (mkArg lab . mkArgTmpVarName meth) $ methArg meth
               return [(PP.text mpath PP.<> (PP.parens $ PP.hsep $ PP.punctuate PP.comma $ args)), PP.text "..."]
    act = case eact of
               Left  e -> [PP.text $ "/* " ++ e ++ " */"]
               Right a -> a

mkITE :: PP.Doc -> [PP.Doc] -> [PP.Doc] -> PP.Doc
mkITE i t e = ((PP.text "if" PP.<+> PP.parens i) PP.<+> (if' (length t /= 1) (PP.char '{') PP.empty))
           PP.$$ (nest' $ PP.vcat $ map (PP.<> PP.semi) t)
           PP.$$ ((if' (length t /= 1) (PP.char '}') PP.empty) PP.<+> (PP.text "else") PP.<+> (if' (length e /= 1) (PP.char '{') $ if' nestedif elcond PP.empty))
           PP.$$ (if' nestedif elbody $ (nest' $ PP.vcat $ map (PP.<> PP.semi) e))
           PP.$$ (if' (length e /= 1) (PP.char '}') PP.empty)
    where eltxt = PP.render $ head e
          nestedif = length e == 1 && isPrefixOf "if (" eltxt
          elcond = PP.text $ head $ lines' eltxt
          elbody = PP.text $ unlines' $ tail $ lines' eltxt

tagToPath :: (?inspec::F.Spec, ?sc::F.Scope) => String -> String
tagToPath tag = intercalate "." $ (map sname path) ++ [mname]
    where F.ScopeMethod _ m = ?sc
          (scid, _) = itreeParseName $ sname m
          (iid, mname) = itreeParseName tag
          Just path = let ?spec = ?inspec in itreeAbsToRelPath scid iid

mkArg :: (?inspec::F.Spec, ?spec::Spec, ?pid::PrID, ?sc::F.Scope) => [(String, VarAsn)] -> String -> PP.Doc
mkArg lab argname = mkArg' lab $ I.EVar argname

mkArg' :: (?inspec::F.Spec, ?spec::Spec, ?pid::PrID, ?sc::F.Scope) => [(String, VarAsn)] -> I.Expr -> PP.Doc
mkArg' lab e =
    case typ e of
         Struct _   -> error "mkArg: Structs are not supported"
         Array _ _  -> error "mkArg: Arrays are not supported"
         VarArray _ -> error "mkArg: VarArrays are not supported"
         _          -> mkScalar lab e

mkScalar :: (?inspec::F.Spec, ?spec::Spec, ?pid::PrID, ?sc::F.Scope) => [(String, VarAsn)] -> I.Expr -> PP.Doc
mkScalar lab e | masn == Nothing = PP.text "/* any value */"
               | otherwise       = PP.hcat $ PP.punctuate (PP.text " ++ ") es'
    where masn = lookup (show e) lab 
          Just (AsnScalar asns) = masn
          (off, es) = foldl' (\(o, exps) ((l,h), v) -> ((h+1), exps ++ (if' (l > o) [anyvalue (l-o)] []) ++ [ppAsn (h-l) v]))
                             (0, []) asns
          es' = es ++ (if' (off < typeWidth e) [anyvalue (typeWidth e - off)] [])
          ppAsn w (Left True)  = anyvalue w
          ppAsn w (Left False) = novalue w
          ppAsn _ (Right x)    = exprToTSL2 ?inspec ?pid ?sc x
          anyvalue w = PP.text $ "/*any value*/" ++ show w  ++ "'h0"
          novalue  w = PP.text $ "/*??? (" ++ show w ++ " bits)*/"


derefStep :: (MonadResource (DDNode s u) (ST s) t) => C.STDdManager s u -> Step s u -> t (ST s) ()
derefStep m (Step cond branch) = do
    let ops@Ops{..} = constructOps m
    $d deref cond
    derefBranch ops branch

derefBranch :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> Branch s u -> t (ST s) ()
derefBranch ops@Ops{..} (BranchITE i t e) = do
    $d deref i
    $d deref t
    derefBranch ops e
derefBranch Ops{..} (BranchAction i t) = do
    $d deref i
    $d deref t
derefBranch _ BranchStuck = return ()

gen1Step :: (MonadResource (DDNode s u) (ST s) t) 
         => Spec 
         -> C.STDdManager s u 
         -> RefineDynamic s u 
         -> DB s u AbsVar AbsVar 
         -> C.DDNode s u 
         -> Lab s u 
         -> DDNode s u 
         -> DDNode s u 
         -> DDNode s u 
         -> [DDNode s u] 
         -> t (ST s) (Step s u)
gen1Step spec m refdyn pdb cont lp set strategy goal regions = do
    let ops@Ops{..} = constructOps m
        DB{_sections=SectionInfo{..}, ..} = pdb
    let ?spec = spec
        ?m    = m
        ?db   = pdb
        ?rd   = refdyn
        ?cont = cont
        ?lp   = lp
    muniqlab <- pickCommonLab strategy goal regions set
    case muniqlab of
         Nothing -> do tagNopCond <- compileExpr (mkTagVar I.=== (I.EConst $ I.EnumVal mkTagDoNothing))
                       -- Use strategy to determine states where $tagnop is a winning action
                       stratinset <- $r2 band set strategy
                       stepWaitCond0 <- $r2 band stratinset tagNopCond
                       $d deref stratinset
                       $d deref tagNopCond
                       stepWaitCond1 <- $r1 (bexists _labelCube) stepWaitCond0
                       $d deref stepWaitCond0
                       stepWaitCond <- (liftM bnot) $ $r1 (bexists _untrackedCube) stepWaitCond1
                       $d deref stepWaitCond1
                       -- Remove these states from set
                       set' <- $r2 band set stepWaitCond
                       -- Iterate through what remains
                       stepBranches <- mkBranches strategy goal regions set'
                       return Step{..}
         Just l  -> do $rp ref bfalse
                       return $ Step btrue (BranchAction set l)

-- consumes input reference
mkBranches :: (MonadResource (DDNode s u) (ST s) t, ?spec::Spec, ?m::C.STDdManager s u, ?rd::RefineDynamic s u, ?db::DB s u AbsVar AbsVar, ?cont::C.DDNode s u, ?lp::Lab s u) 
           => DDNode s u 
           -> DDNode s u 
           -> [DDNode s u] 
           -> DDNode s u -> t (ST s) (Branch s u)
mkBranches strategy goal regions set = do
    let RefineDynamic{..} = ?rd
    muniqlab <- pickCommonLab strategy goal regions set
    case muniqlab of
         Just l  -> return $ BranchAction set l
         Nothing -> mkBranches' strategy goal regions set

-- consumes input reference
pickCommonLab :: (MonadResource (DDNode s u) (ST s) t, ?spec::Spec, ?m::C.STDdManager s u, ?rd::RefineDynamic s u, ?db::DB s u AbsVar AbsVar, ?cont::C.DDNode s u, ?lp::Lab s u) 
              => DDNode s u 
              -> DDNode s u 
              -> [DDNode s u] 
              -> DDNode s u -> t (ST s) (Maybe (DDNode s u))
pickCommonLab strategy goal regions set = do
    let ops@Ops{..} = constructOps ?m
        DB{_sections=sinfo@SectionInfo{..}, ..} = ?db
        RefineDynamic{..} = ?rd
        sd = SynthData sinfo trans ?cont ?rd ?lp
    muniqlab <- pickLabel2 ops sd regions goal strategy set
    case muniqlab of
         Just (l, farthest) -> do itr <- CG.enumerateEquivalentLabels ops sd set l
                                  mlab' <- pickProgressLabel farthest set itr
                                  case mlab' of
                                       Nothing -> return Nothing
                                       Just l' -> return $ Just l'
         Nothing            -> return Nothing


-- Iterate through labels returned by pickLabel2 looking for one that guarantees progress
pickProgressLabel :: (MonadResource (DDNode s u) (ST s) t, ?m::C.STDdManager s u, ?rd::RefineDynamic s u, ?db::DB s u AbsVar AbsVar, ?cont::C.DDNode s u, ?lp::Lab s u) 
                  => DDNode s u 
                  -> DDNode s u 
                  -> CG.IteratorM (t (ST s)) (DDNode s u) 
                  -> t (ST s) (Maybe (DDNode s u))
pickProgressLabel _        _   CG.Empty          = return Nothing
pickProgressLabel farthest set (CG.Item l stitr) = do
    let ops@Ops{..} = constructOps ?m
        RefineDynamic{..} = ?rd
    outerRegion <- $r2 band set farthest
    trel <- $r $ C.conj ops $ l:(map snd trans)
    suc <- simulateControllable set trel
    $d deref trel
    outerRegion' <- $r2 band suc farthest
    $d deref suc
    shrinks <- lift $ leq outerRegion' outerRegion
    newstates <- $r2 band outerRegion' (bnot outerRegion)
    $d deref outerRegion
    $d deref outerRegion'
    if shrinks && outerRegion' /= outerRegion
       then return $ Just l
       else do $d deref l
               itr <- stitr
               pickProgressLabel farthest set itr
   
-- Called when none of the labels returned by pickLabel2 are sutable.
-- Uses ifCondition/pickLabel to split set into subregions.
mkBranches' :: (MonadResource (DDNode s u) (ST s) t, ?spec::Spec, ?m::C.STDdManager s u, ?rd::RefineDynamic s u, ?db::DB s u AbsVar AbsVar, ?cont::C.DDNode s u, ?lp::Lab s u) 
            => DDNode s u 
            -> DDNode s u 
            -> [DDNode s u] 
            -> DDNode s u -> t (ST s) (Branch s u) 
mkBranches' strategy goal regions set = do
    let ops@Ops{..} = constructOps ?m
        DB{_sections=sinfo@SectionInfo{..}, ..} = ?db
        RefineDynamic{..} = ?rd
        sd = SynthData sinfo trans ?cont ?rd ?lp
    mcond <- ifCondition ops sd strategy set
    case mcond of
         Nothing   -> do $d deref set
                         return $ BranchStuck 
         Just cond -> do condset  <- $r2 band set cond
                         Just act <- pickLabel ops sd strategy condset
                         $d deref condset
                         set'     <- $r2 band set (bnot cond)
                         $d deref set
                         if set' == bfalse
                            then do $d deref set'
                                    return $ BranchAction cond act
                            else do branch' <- mkBranches strategy goal regions set'
                                    return $ BranchITE cond act branch'

-- Decomposes cond into prime implicants and converts it to a boolean expression
mkCondition :: (MonadResource (DDNode s u) (ST s) t, ?spec::Spec, ?m::C.STDdManager s u, ?db::DB s u AbsVar AbsVar) => DDNode s u -> t (ST s) I.Expr
mkCondition cond = do
    let ops@Ops{..} = constructOps ?m
    cubes_ <- lift $ C.primeCover ops cond
    cubes <- mapM ($r . return) cubes_
    res <- (liftM I.disj) $ mapM mkCondCube cubes
    mapM_ ($d deref) cubes
    return res

mkCondCube :: (MonadResource (DDNode s u) (ST s) t, ?spec::Spec, ?m::C.STDdManager s u, ?db::DB s u AbsVar AbsVar) => DDNode s u -> t (ST s) I.Expr
mkCondCube cub = do
   let DB{_symbolTable = SymbolInfo{..}, ..} = ?db
   let ops@Ops{..} = constructOps ?m
   asns <- cubeToAsns ops cub $ map (mapSnd sel2) $ M.toList _stateVars 
   return $ trace ("mkCondCube " ++ show asns)
          $ I.conj 
          $ map (\(av, vals) -> I.disj $ map (formToExpr . avarAsnToFormula av) vals) asns

    
cubeToAsns :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> DDNode s u -> [(AbsVar, [Int])] -> t (ST s) [(AbsVar, [Integer])]
cubeToAsns Ops{..} rel vs = do
    supp <- lift $ supportIndices rel
    asn  <- lift $ satCube rel
    let supvars = filter (any (\idx -> elem idx supp) . snd) vs
    return $ map (\(av, is) -> (av, map boolArrToBitsBe $ (<$*>) $ map (C.expand . (asn !!)) is))
           $ nub supvars

cubeToAsn :: (MonadResource (DDNode s u) (ST s) t) => Ops s u -> DDNode s u -> [(AbsVar, [Int])] -> t (ST s) [(AbsVar, [Bool])]
cubeToAsn Ops{..} rel vs = do
    supp <- lift $ supportIndices rel
    asn  <- lift $ satCube rel
    let supvars = filter (any (\idx -> elem idx supp) . snd) vs
    return $ map (\(av, is) -> (av, map (satBitToBool . (asn !!)) is))
           $ nub supvars
    where satBitToBool Zero  = False
          satBitToBool One   = True
          satBitToBool _     = False

mkLabel :: (MonadResource (DDNode s u) (ST s) t, ?m::C.STDdManager s u, ?db::DB s u AbsVar AbsVar) => DDNode s u -> t (ST s) [(AbsVar, [Bool])]
mkLabel lab = do
    let DB{_symbolTable = SymbolInfo{..}, ..} = ?db
    let ops@Ops{..} = constructOps ?m
    lab' <- $r $ C.largePrime ops lab
    asn <- cubeToAsn ops lab' $ map (mapSnd sel2) $ M.toList _labelVars
    $d deref lab'
    return asn
