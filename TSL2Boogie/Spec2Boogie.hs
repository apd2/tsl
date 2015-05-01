{-# LANGUAGE RecordWildCards, ImplicitParams, TupleSections, ScopedTypeVariables #-}

module TSL2Boogie.Spec2Boogie(spec2Boogie) where

import qualified Data.Map             as M
import Data.Maybe
import Data.List
import qualified Data.Graph.Inductive as IG
import qualified Data.Graph.Dom       as G
import Data.Tuple.Select
import Text.PrettyPrint

import PP
import Ops
import Util
import Internal.CFA
import Internal.ISpec
import Internal.ITransducer
import Internal.IVar
import Internal.IType
import Internal.IExpr


type Path = [String]

ppPath p = hcat $ punctuate (char '.') (map text p)

-- alphabet symbol: input port name:field names. [] = init symbol
type Symbol = [String]

showSymbol s = render $ hcat $ punctuate (char '.') (map text s)

spec2Boogie :: Spec -> Either String Doc
spec2Boogie spec = let ?spec = spec in
                   if any ((== "main") . txName) $ specXducers spec
                      then Right mkMainXducer
                      else Left "no main transducer found"

mkMainXducer :: (?spec::Spec) => Doc
mkMainXducer = vcat $ [collectTypes, pp "" {-: map mkVar vs-}, xducers]
    where -- vs      = collectVars [] $ getXducer "main"
          xducers = mkXducer [] (getXducer "main") []

getXducer :: (?spec::Spec) => String -> Transducer
getXducer n = fromJustMsg ("fromJust Nothing getXducer" {-intercalate "," $ n : (map txName $ specXducers ?spec)-}) $ find ((== n) . txName) $ specXducers ?spec

collectTypes :: (?spec::Spec) => Doc
collectTypes = vcat $ stenums ++ (map (uncurry mkType) $ foldl' add [] types)
    where add :: [(Type, [String])] -> Type -> [(Type, [String])]
          add []      t = [(t,[])]
          add ((t0,as):ts) t = case (t0,t) of
                                    (Struct _ fs1, Struct (Just n2) fs2) -> if' (fs1 == fs2) ((t0,n2:as):ts) ((t0,as):(add ts t))
                                    _                                    -> (t0,as):(add ts t)
          types = nub $ concatMap collectTypes' $ specXducers ?spec
          -- state enum
          stenums = mapMaybe (\x -> case txBody x of
                                         Left _        -> Nothing
                                         Right (cfa,_) -> Just $ mkEnumType n $ map (render . stateName x) locs
                                                          where locs = delete cfaInitLoc (cfaDelayLocs cfa)
                                                                n = render $ stateTypeName x)
                    $ specXducers ?spec

collectTypes' :: (?spec::Spec) => Transducer -> [Type]
collectTypes' Transducer{..} = 
    case txBody of
         Left _        -> []
         Right (_, vs) -> nub $ (concatMap (collectTypesT . varType) vs) ++ 
                                (collectTypesT txOutType) ++ 
                                (concatMap (collectTypesT . fst) txInput)

-- Bools and bitvectors are builtins in Boogie - ignore them.
-- Strip sequence types.
collectTypesT :: (?spec::Spec) => Type -> [Type]
collectTypesT t@(Enum _ _)     = [t]
collectTypesT t@(Struct _ fs)  = nub $ t:(concatMap (\(Field _ t) -> collectTypesT t) fs)
collectTypesT   (Ptr _ _)      = error "Pointer type in transducer"
collectTypesT   (Seq _ t)      = collectTypesT t         
collectTypesT t@(Array _ t' _) = nub $ t:(collectTypesT t')
collectTypesT   (VarArray _ _) = error "VarArray type in transducer"
collectTypesT   _              = []

typeName :: Type -> Doc
typeName (Bool _)            = text "bool"
typeName (SInt _ _)          = error "Not implemented: signed bitvectors in Spec2Boogie.hs"
typeName (UInt _ w)          = text $ "bv" ++ show w
typeName (Enum _ e)          = text e
typeName (Struct Nothing _)  = error "Not implemented: anonymous struct in Spec2Boogie.hs"
typeName (Struct (Just n) _) = text n
typeName (Array _ _ _)       = error "Not implemented: arrays in Spec2Boogie.hs"
typeName t                   = error $ "typeName " ++ show t


mkEnumType :: String -> [String] -> Doc
mkEnumType n es = (text "type" <+> {-text "finite" <+>-} text n <> semi)
                  $$
                  (vcat $ map (\e -> text "const" <+> text "unique" <+> text e <> colon <+> text n <> semi) es)
                  $$
                  (text "axiom" <+> parens (text "forall" <+> text "_x" <> colon <+> text n <> text "::" <+> disj) <> semi)
    where disj = hcat $ punctuate (text "||") $ map (\e -> text "_x" <+> text "==" <+> text e) es

mkType :: (?spec::Spec) => Type -> [String] -> Doc
mkType (Enum _ n)  _    = mkEnumType n es
    where Enumeration _ es = getEnumeration n 
mkType (Struct mn fs) as = (text "type" <+> text "{:datatype}" <+> pp n <> semi)
                           $$
                           (text "function" <+> text "{:constructor}" <+> pp n <> parens args) <+> colon <+> pp n <> semi
                           $$
                           (vcat $ map (\a -> text "type" <+> text a <+> char '=' <+> pp n <> semi) as)
    where Just n = mn
          args = hsep
                 $ punctuate comma
                 $ map (\(Field nm t) -> text nm <> colon <> typeName t)
                 $ filter (not . isSeq) fs

mkXducer :: (?spec::Spec) => Path -> Transducer -> [(Path, String)] -> Doc
mkXducer p x fanout =
    case txBody x of
         -- composite transducer
         Left is -> -- print instances; route each instance output to other instance inputs or to the top-level output
                    vcat $ punctuate (text "") 
                    $ (mapIdx (\i id -> mkXducer (p++[tiInstName i]) (getXducer $ tiTxName i) (connect id)) is)
                    where -- compute list of ports that an instance is connected to
                          connect :: Int -> [(Path, String)]
                          connect id | id == length is - 1 = fanout ++ ports
                                     | otherwise           = ports
                                     where 
                                     name = tiInstName $ is !! id
                                     ports = concatMap (\TxInstance{..} -> map (\(_,(_,port)) -> (p++[tiInstName], port)) 
                                                                           $ filter ((== name) . fst) 
                                                                           $ zip tiInputs (txInput $ getXducer tiTxName)) is
         -- simple transducer
         Right (_,vs) -> let spec = ?spec 
                             invars = map (\(t,nm) -> Var False VarState nm t) $ txInput x
                             outvar = Var False VarState (txName x) $ txOutType x in
                         let ?spec = spec {specVar = vs ++ invars ++ [outvar]} in
                         mkXducer' p x fanout
         

call :: Doc -> [Doc] -> Doc
call f args = text "call" <+> f <+> (parens $ hsep $ punctuate comma args) <> semi

assign :: Doc -> Doc -> Doc
assign l r = l <+> text ":=" <+> r <> semi

var :: Doc -> Doc -> Doc
var n t = text "var" <+> n <+> char ':' <+> t <> semi

-- Print simple transducer:
mkXducer' :: (?spec::Spec) => Path -> Transducer -> [(Path, String)] -> Doc
mkXducer' p x@Transducer{..} fanout = vcat $ punctuate (text "") (vars:handlers)
    where 
    Right (cfa, vs) = txBody

    insymbols::[Symbol] = concatMap (\(t,n) -> symbols' t [n]) txInput
    outsymbols::[Symbol] = symbols' txOutType [txName]

    symbols' :: Type -> Symbol -> [Symbol]
    symbols' (Seq _ (Struct _ fs)) ns = (concatMap (\(Field fn ft) -> symbols' ft (ns++[fn])) fs) ++ [ns]
    symbols' (Seq _ (Seq    _ t))  ns = symbols' t (ns++["<>"])
    symbols' (Seq _ t)             ns = [ns]
    symbols' _                     _  = []

    -- states along with the symbol acceped in each state
    states :: [(Loc,Maybe Symbol)]
    states = map (\loc -> if' (loc == cfaInitLoc) (loc, Just [])
                              (case cfaLocLabel loc cfa of
                                    LFinal _ _ _ -> (loc, Nothing)
                                    LAdvance _ e -> (loc, Just $ expr2Sym e)))
             $ cfaDelayLocs cfa 

    expr2Sym :: Expr -> Symbol
    expr2Sym (EVar n)               = [n]
    expr2Sym (EField (ESeqVal e) f) = (expr2Sym e)++[f]
    expr2Sym (ESeqVal e)            = (expr2Sym e)++["<>"]

    sym2Expr :: Symbol -> Expr
    sym2Expr [port] = ESeqVal $ EVar port
    sym2Expr sym    = if last sym == "<>"
                         then ESeqVal $ sym2Expr $ init sym
                         else ESeqVal $ EField (sym2Expr $ init sym) (last sym)
                      
    symbolType = exprType . sym2Expr

    ([(initst,_)], states') = partition (null . fromJustMsg "mkXducer" . snd) $ filter (isJust . snd) states
    -- transition CFAs
    (initSink, initCFA) = cfaAddUniqueSink $ cfaLocTransCFA cfa initst
    cfas::M.Map Symbol [(Loc,Loc,CFA)] 
    cfas = M.fromList
           $ map (\ss -> (fromJustMsg "mkXducer" $ snd $ head ss, map ((\l -> let (sink, cfa') = cfaAddUniqueSink $ cfaLocTransCFA cfa l
                                                                in (l, sink, cfa')) . fst) ss))
           $ sortAndGroup snd states'

    -- the post-dominator algorithm requires a unique sink
    cfaAddUniqueSink :: CFA -> (Loc, CFA)
    cfaAddUniqueSink cfa = (sink, foldl' (\c loc -> cfaInsTrans loc sink TranNop c) cfa' $ cfaSink cfa)
        where (cfa',sink) = cfaInsLoc (LInst ActNone) cfa

    -- state var
    stvar = var (stateVarName p) (stateTypeName x)

    -- local vars
    lvars = map (\v -> var (xvarName p $ varName v) (typeName $ varType v)) vs

    -- generate variables to store input and output symbols
    invars  = map mkSymVar insymbols
    outvars = map mkSymVar outsymbols

    vars = vcat $ stvar : text "" : invars ++ text "" : outvars ++ text "" : lvars

    mkSymVar :: Symbol -> Doc
    mkSymVar s = var (symVarName p s) (typeName $ symbolType s)

    -- init method
    initproc = (text "procedure" <+> initializerName p <+> (parens empty)) $+$ lbrace $+$ (nest' $ mkCFA (initst, initSink, initCFA)) $+$ rbrace

    -- input handlers
    handlers = map mkHandler insymbols

    mkHandler :: Symbol -> Doc
    mkHandler sym = sig $+$ lbrace $+$ nest' body $+$ rbrace
        where
        -- procedure signature
        sig =  text "procedure" <+> handlerName p sym 
           <+> (parens $ symVarName [] sym <> colon <> (typeName $ symbolType sym))
        -- save input symbol and eof flag
        readinp = assign (symVarName p sym) (symVarName [] sym)

        -- for each state where sym is handled, generate code from CFA
        handlers = maybe [] 
                         (map (\(loc, sink, cfa) -> (stateVarName p <+> pp "==" <+> stateName x loc, mkCFA (loc, sink, cfa))))
                         (M.lookup sym cfas)

        -- generate empty handlers (loop transitions) for all states where sym's parent is handled
        parents = init $ tail $ inits sym
        parentlocs = concatMap (\sym' -> maybe [] (map sel1) $ M.lookup sym' cfas) parents
        loops = if null parents 
                   then []
                   else [(hsep $ punctuate (text "&&") $ map (\loc -> stateVarName p <+> text "==" <+> stateName x loc) parentlocs, empty)]

        body = mkSwitch (handlers ++ loops ++ [(undefined, text "assert(false);")])

    mkSwitch :: [(Doc, Doc)] -> Doc
    mkSwitch [(_,defaction)]       = defaction -- throw error otherwise
    mkSwitch ((cond, action):rest) = ((text "if" <+> (parens cond) <+> lbrace) $+$ (nest' action))
                                     $+$ 
                                     (if' (null $ tail rest)
                                          ((rbrace <+> text "else" <+> lbrace) $+$ (nest' $ mkSwitch rest) $+$ rbrace)
                                          (zeroWidthText "} else " <> mkSwitch rest))

    mkCFA :: (Loc, Loc, CFA) -> Doc
    mkCFA (from, sink, cfa) = mkCFA' (from, sink, cfa) sink
    
    mkCFA' :: (Loc, Loc, CFA) -> Loc -> Doc
    mkCFA' (from, sink, cfa) to | from == to        = empty                                             -- stop at the "to" node
                                | loc0 == sink      = assign (stateVarName p) (stateName x from)        -- final location
                                | null (tail trans) = mkTransition lab0 $+$ mkCFA' (loc0, sink, cfa) to -- single successor
                                | otherwise         = (mkSwitch 
                                                        $ map (\(tlab,loc) -> (text "*", mkTransition tlab $+$ mkCFA' (loc, sink,cfa) pdom)) trans)
                                                       $+$
                                                       mkCFA' (pdom, sink, cfa) to 
        where trans@((lab0,loc0):_) = cfaSuc from cfa
              -- postdominator of from
              --doms = G.idom (sink, G.fromEdges $ map swap $ IG.edges cfa)
              cfa'::CFA = IG.mkGraph (IG.labNodes cfa) $ map (\(from, to, l) -> (to,from,l)) $ IG.labEdges cfa
              doms = IG.iDom cfa' sink
              pdom = fromJustMsg "mkCFA" $ lookup from doms 

    mkTransition :: TranLabel -> Doc
    mkTransition (TranStat (SAssume e))   = text "assume" <> (parens $ mkExpr e) <> semi
    mkTransition (TranStat (SAssert e))   = text "assert" <> (parens $ mkExpr e) <> semi
    mkTransition (TranStat (SAssign l r)) = assign (mkExpr l) (mkExpr r)
    mkTransition (TranStat (SAdvance e))  = mkAdvance e
    mkTransition TranNop                  = empty

    mkAdvance :: Expr -> Doc
    mkAdvance exp = out $+$ randomize
        where sym = expr2Sym exp
              -- output current symbol value
              out = output sym
              output s = vcat 
                         $ map (\(path,port) -> call (handlerName path (port:tail s)) [symVarName p s])
                         $ fanout
              -- randomize it
              randomize = text "havoc" <+> symVarName p sym <> semi

    mkExpr :: Expr -> Doc
    mkExpr (ESeqVal e)             = symVarName p $ expr2Sym e
    mkExpr (EVar v)                = xvarName p v
    mkExpr (EConst v)              = mkConst v
    mkExpr (EField e f)            = let tn = typeName $ exprType e in text f <> char '#' <> tn <> (parens $ mkExpr e)
    mkExpr (EUnOp Not e)           = parens $ char '!' <> mkExpr e
    mkExpr (EUnOp BNeg e)          = text ("BV"++(show $ exprWidth e)++"_NOT") <> (parens $ mkExpr e)
    mkExpr (EBinOp Eq e1 e2)       = parens $ mkExpr e1 <+> text "==" <+> mkExpr e2
    mkExpr (EBinOp Neq e1 e2)      = parens $ mkExpr e1 <+> text "!=" <+> mkExpr e2
    mkExpr (EBinOp Lt e1 e2)       = bvbop "ULT" e1 e2
    mkExpr (EBinOp Gt e1 e2)       = bvbop "UGT" e1 e2
    mkExpr (EBinOp Lte e1 e2)      = bvbop "ULEQ" e1 e2
    mkExpr (EBinOp Gte e1 e2)      = bvbop "UGEQ" e1 e2
    mkExpr (EBinOp And e1 e2)      = parens $ mkExpr e1 <+> text "&&" <+> mkExpr e2
    mkExpr (EBinOp Or e1 e2)       = parens $ mkExpr e1 <+> text "||" <+> mkExpr e2
    mkExpr (EBinOp Imp e1 e2)      = parens $ mkExpr e1 <+> text "==>" <+> mkExpr e2
    mkExpr (EBinOp BAnd e1 e2)     = bvbop "AND" e1 e2
    mkExpr (EBinOp BOr e1 e2)      = bvbop "OR" e1 e2
    mkExpr (EBinOp BXor e1 e2)     = bvbop "XOR" e1 e2
    mkExpr (EBinOp BConcat e1 e2)  = parens $ mkExpr e2 <+> text "++" <+> mkExpr e1
    mkExpr (EBinOp Plus e1 e2)     = bvbop "ADD" e1 e2
    mkExpr (EBinOp BinMinus e1 e2) = bvbop "SUB" e1 e2
    mkExpr (EBinOp Mul e1 e2)      = bvbop "MULT" e1 e2
    mkExpr (ESlice e (l,h))        = mkExpr e <> (brackets $ pp h <> char ':' <> pp l)

    bvbop op e1 e2 = text ("BV"++(show $ exprWidth e1)++op) <> (parens $ mkExpr e1 <> comma <+> mkExpr e2)

    mkConst :: Val -> Doc
    mkConst (BoolVal True)     = pp "true"
    mkConst (BoolVal False)    = pp "false"
    mkConst (UIntVal w v)      = pp v <> text "bv" <> pp w
    mkConst (EnumVal n)        = pp n

xvarName :: Path -> String -> Doc
xvarName p v = ppPath p <> char '$' <> pp v

symVarName :: Path -> Symbol -> Doc
symVarName p s = xvarName p $ showSymbol s

handlerName :: Path -> Symbol -> Doc
handlerName p s = xvarName p $ "handle_" ++ showSymbol s

stateVarName :: Path -> Doc
stateVarName p = xvarName p "$state"

stateName :: Transducer -> Loc -> Doc
stateName x l = (text $ txName x) <> pp "$$" <> pp l

stateTypeName :: Transducer -> Doc
stateTypeName x = (pp $ txName x) <> pp "_state_t"

initializerName :: Path -> Doc 
initializerName p = ppPath p <> pp "$$init"
