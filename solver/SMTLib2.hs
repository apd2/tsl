{-# LANGUAGE ImplicitParams #-}

-- Interface to SMT2 format

module SMTLib2() where

import qualified Text.Parsec as P
import Text.PrettyPrint
import System.IO.Unsafe
import System.Process
import System.Exit
import Control.Monad.Error
import Control.Applicative hiding (many,optional,Const,empty)
import Data.List
import qualified Data.Set             as S
import qualified Data.Map             as M

import Util
import Predicate
import BFormula
import ISpec
import IVar
import IType
import SMTLib2Parse
import Store

data SMT2Config = SMT2Config {
    s2Solver :: String,  -- Name of the solver executable
    s2Opts   :: [String] -- Arguments passed on every invocation of the solver
}

------------------------------------------------------
-- Printing formulas in SMTLib2 format
------------------------------------------------------

class SMTPP a where
    smtpp :: a -> Doc

mkFormulas :: (?spec::Spec) => [Formula] -> (Doc, [(String, Term)])
mkFormulas fs = 
    let vars = S.toList $ S.fromList $ concatMap fVar fs
        (typemap, typedecls) = mkTypeMap vars in
    let ?typemap = typemap in
    let (ptrvars, ptrconstr, ptrmap) = mkPtrConstraints fs in
        (-- type declarations
         typedecls 
         $+$
         -- variable declarations
         (vcat $ map smtpp vars)
         $+$
         ptrvars
         $+$
         -- formulas
         (vcat $ mapIdx (\f i -> parens $ text "assert" 
                                          <+> (parens $ char '!' <+> smtpp f <+> text ":named" <+> text "a" <> int i)) fs)
         $+$
         -- pointer consistency constraints
         ptrconstr
         ,
         ptrmap)

instance (?spec::Spec, ?typemap::M.Map Type String) => SMTPP Var where
    smtpp v = parens $  text "declare-const"
                    <+> text (mkIdent $ varName v)
                    <+> text (?typemap M.! (varType v))

-- convert string into a valid smtlib identifier by
-- bracketing it with '|' if necessary
mkIdent :: String -> String
mkIdent str = if valid then str else "|" ++ str ++ "|"
    where valid = all (\c -> elem c ("_"++['a'..'z']++['A'..'Z']++['0'..'9'])) str
                  && notElem (head str) ['0'..'9']

mkTypeMap :: (?spec::Spec) => [Var] -> (M.Map Type String, Doc)
mkTypeMap vs = foldl' mkTypeMap' (M.empty, empty) alltypes
    where -- sort all types occurring in the spec in dependency order
          alltypes = sortBy (\t1 t2 -> if' (elem t1 $ subtypesRec t2) LT $
                                       if' (elem t2 $ subtypesRec t1) GT $
                                       EQ)
                     $ nub $ concatMap (subtypesRec . typ) vs

mkTypeMap' :: (?spec::Spec) => (M.Map Type String, Doc) -> Type -> (M.Map Type String, Doc)
mkTypeMap' (m,doc) t = let (tname, tdecl) = mkTypeMap1 m t
                       in (M.insert t tname m, doc $$ tdecl)

subtypes :: Type -> [Type]
subtypes Bool        = []
subtypes (SInt _)    = []
subtypes (UInt _)    = []
subtypes (Enum _)    = []
subtypes (Struct fs) = map typ fs
subtypes (Array t _) = [t]
subtypes (Ptr t)     = [t]

subtypesRec :: Type -> [Type]
subtypesRec t = t:(concatMap subtypesRec $ subtypes t)

mkTypeMap1 :: (?spec::Spec) => M.Map Type String -> Type -> (String, Doc)
mkTypeMap1 _ Bool        = ( "Bool"                                  
                           , empty)
mkTypeMap1 _ (SInt w)    = ( "(_ BitVec " ++ show w ++ ")"
                           , empty)
mkTypeMap1 _ (UInt w)    = ( "(_ BitVec " ++ show w ++ ")"
                           , empty)
mkTypeMap1 _ (Enum n)    = ( n
                           , parens $ text "declare-datatypes ()" <+> (parens $ parens $ hsep $ map text $ n:(enumEnums $ getEnumeration n)))
mkTypeMap1 m (Struct fs) = ( tname
                           , parens $ text "declare-datatypes ()" 
                                      <+> (parens $ parens $ text tname 
                                           <+> parens (text ("mk-" ++ tname) <+> (hsep $ map (\(Field n t) -> parens $ text (tname ++ n) <+> text (m M.! t)) fs))))
                           where tname = "Struct" ++ (show $ M.size m)
mkTypeMap1 m (Ptr t)     = ( tname
                           , parens $ text "declare-sort" <+> text tname)
                           where tname = ptrTypeName m t
mkTypeMap1 m (Array t s) = ( "(Array Int " ++ m M.! t ++ ")"
                           , empty)

ptrTypeName :: (Typed a) => M.Map Type String -> a -> String
ptrTypeName m t = mkIdent $ "Ptr" ++ (m M.! typ t)

addrofVarName :: Term -> String
addrofVarName t = mkIdent $ "addrof-" ++ show t

instance (?spec::Spec, ?typemap::M.Map Type String) => SMTPP Formula where
    smtpp FTrue             = text "true"
    smtpp FFalse            = text "false"
    smtpp (FPred p)         = smtpp p
    smtpp (FBinOp op f1 f2) = parens $ smtpp op <+> smtpp f1 <+> smtpp f2
    smtpp (FNot f)          = parens $ text "not" <+> smtpp f

instance (?spec::Spec, ?typemap::M.Map Type String) => SMTPP Predicate where
    smtpp (PAtom op t1 t2) = parens $ smtpp op <+> smtpp t1 <+> smtpp t2

instance (?spec::Spec, ?typemap::M.Map Type String) => SMTPP Term where
    smtpp (TVar n)               = text $ mkIdent n
    smtpp (TSInt w v) |v>=0      = text $ "(_ bv" ++ show v ++ " " ++ show w ++ ")"
                      |otherwise = text $ "(bvneg (_ bv" ++ show (-v) ++ " " ++ show w ++ "))"
    smtpp (TUInt w v)            = text $ "(_ bv" ++ show v ++ " " ++ show w ++ ")"
    smtpp (TEnum n)              = text n
    smtpp TTrue                  = text "true"
    smtpp (TAddr t)              = text $ addrofVarName t
    smtpp (TField t f)           = parens $ text ((?typemap M.! typ t) ++ f) <+> smtpp t
    smtpp (TIndex a i)           = parens $ text "select" <+> smtpp a <+> smtpp i
    smtpp (TUnOp op t)           = parens $ smtpp op <+> smtpp t
    smtpp (TBinOp op t1 t2)      = parens $ smtpp op <+> smtpp t1 <+> smtpp t2
    smtpp (TSlice t (l,h))       = parens $ (parens $ char '_' <+> text "extract" <+> int l <+> int h) <+> smtpp t

instance SMTPP RelOp where
    smtpp REq  = text "="
    smtpp RLt  = text "bvslt"
    smtpp RGt  = text "bvsgt"
    smtpp RLte = text "bvsle"
    smtpp RGte = text "bvsge"

instance SMTPP ArithUOp where
    smtpp AUMinus = text "bvneg"
    smtpp ABNeg   = text "bvnot"

instance SMTPP ArithBOp where
    smtpp ABAnd     = text "bvand"
    smtpp ABOr      = text "bvor"
    smtpp ABXor     = text "bvxor"
    smtpp ABConcat  = text "concat"
    smtpp APlus     = text "bvadd"
    smtpp ABinMinus = text "bvsub"
    smtpp AMod      = text "bvsmod"
    smtpp AMul      = text "bvmul"

instance SMTPP BoolBOp where
    smtpp Conj      = text "and"
    smtpp Disj      = text "or"
    smtpp Impl      = text "=>"
    smtpp Equiv     = text "="

------------------------------------------------------
-- Pointer-related stuff
------------------------------------------------------

-- Consider all pairs of address-of terms of matching 
-- types that occur in the formulas and generate
-- conditions on when these terms are equal, namely:
-- * &x != &y if x and y are distinct variables
-- * &x[i] == &x[j] iff i==j
-- Returns:
-- * a bunch of constant declarations, one for 
--   each address-of term that occurs in the formulas 
-- * the generated condition over these variables
-- * a map from constant names to the terms they represent
mkPtrConstraints :: (?spec::Spec, ?typemap::M.Map Type String) => [Formula] -> (Doc, Doc, [(String, Term)])
mkPtrConstraints fs =
    (vcat $ map mkAddrofVar addrterms,
     parens 
     $ ((text "and") <+> )
     $ hsep 
     $ concatMap (map (smtpp . ptrEqConstr) . pairs)
     $ sortAndGroup typ addrterms,
     map (\t -> (addrofVarName t, t)) addrterms)
    where addrterms = nub $ concatMap faddrofTerms fs
          

mkAddrofVar :: (?spec::Spec, ?typemap::M.Map Type String) => Term -> Doc
mkAddrofVar t = parens $ text "declare-const" 
                     <+> text (addrofVarName t)
                     <+> text (ptrTypeName ?typemap t)

faddrofTerms :: (?spec::Spec, ?typemap::M.Map Type String) => Formula -> [Term]
faddrofTerms FTrue                   = []
faddrofTerms FFalse                  = []
faddrofTerms (FPred (PAtom _ t1 t2)) = taddrofTerms t1 ++ taddrofTerms t2
faddrofTerms (FBinOp _ f1 f2)        = faddrofTerms f1 ++ faddrofTerms f2
faddrofTerms (FNot f)                = faddrofTerms f

taddrofTerms :: Term -> [Term]
taddrofTerms (TAddr t) = [t]
taddrofTerms _         = []

ptrEqConstr :: (?spec::Spec, ?typemap::M.Map Type String) => (Term, Term) -> Formula
ptrEqConstr (t1, t2) = case ptrEqCond t1 t2 of
                           FFalse -> neq (TAddr t1) (TAddr t2)
                           f      -> FBinOp Equiv (eq (TAddr t1) (TAddr t2)) f

eq  t1 t2 = FPred $ PAtom REq t1 t2
neq t1 t2 = FNot $ eq t1 t2

ptrEqCond :: (?spec::Spec, ?typemap::M.Map Type String) => Term -> Term -> Formula
ptrEqCond t1@(TField s1 f1) t2@(TField s2 f2) | f1 == f2 = ptrEqCond s1 s2
ptrEqCond t1@(TIndex a1 i1) t2@(TIndex a2 i2)            = fconj [ptrEqCond a1 a2, eq i1 i2]
ptrEqCond t1@(TSlice v1 s1) t2@(TSlice v2 s2) | s1 == s2 = ptrEqCond v1 v2
ptrEqCond _                 _                            = FFalse

------------------------------------------------------
-- Running solver in different modes
------------------------------------------------------

runSolver :: SMT2Config -> Doc -> P.Parsec String () a -> a
runSolver cfg spec parser = 
    let (retcode, out, err) = unsafePerformIO $ readProcessWithExitCode (s2Solver cfg) (s2Opts cfg) (show spec)
    in if retcode == ExitSuccess 
          then case P.parse parser "" out of
                    Left e  -> error $ "Error parsing SMT solver output: " ++ show e
                    Right x -> x
          else error $ "Error running SMT solver: " ++ err

checkSat :: (?spec::Spec) => SMT2Config -> [Formula] -> Maybe Bool
checkSat cfg fs = runSolver cfg spec satresParser
    where spec = (fst $ mkFormulas fs)
              $$ text "(check-sat)"


getUnsatCore :: (?spec::Spec) => SMT2Config -> [Formula] -> Maybe [Int]
getUnsatCore cfg fs =
    runSolver cfg spec
    $ do res <- satresParser
         case res of
              Just False -> liftM Just unsatcoreParser
              _          -> return Nothing
    where spec = text "(set-option :produce-unsat-cores true)"
              $$ (fst $ mkFormulas fs)
              $$ text "(check-sat)"
              $$ text "(get-unsat-core)"

getModel :: (?spec::Spec) => SMT2Config -> [Formula] -> Maybe Store
getModel cfg fs =
    runSolver cfg spec
    $ do res <- satresParser
         case res of 
              Just True -> liftM Just $ modelParser ptrmap
              _         -> return Nothing
    where (spec0, ptrmap) = mkFormulas fs
          spec = spec0
              $$ text "(check-sat)"
              $$ text "(get-model)"
