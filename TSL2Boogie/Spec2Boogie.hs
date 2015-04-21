{-# LANGUAGE RecordWildCards, ImplicitParams, TupleSections, ScopedTypeVariables #-}

module TSL2Boogie.Spec2Boogie(spec2Boogie) where

import qualified Data.Map       as M
import Data.Maybe
import Data.List
import Text.PrettyPrint
import qualified Data.Graph.Dom as G

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

instance PP Path where
    pp p = hcat $ punctuate (char '.') (map text p)

-- alphabet symbol: input port name:field names. [] = init symbol
type Symbol = [String]
instance PP Symbol  where
    pp s = hcat $ punctuate (char '.') (map text s)

data XVar = XVar Path Var

xvName :: Path -> String -> Doc
xvName p v = hcat $ punctuate (char '.') (map text $ p ++ [v])

spec2Boogie :: Spec -> Maybe Doc
spec2Boogie spec = let ?spec = spec in
                   if any ((== "main") . txName) $ specXducers spec
                      then Just mkMainXducer
                      else Nothing

mkMainXducer :: (?spec::Spec) => Doc
mkMainXducer = (vcat $ types ++ map mkVar vs) $+$ xducers
    where vs      = collectVars [] $ getXducer "main"
          types   = vcat $ map collectTypes $ specXducers ?spec
          xducers = mkXducer [] (getXducer "main") []

getXducer :: (?spec::Spec) => String -> Transducer
getXducer = fromMaybe $ find ((== "main") . txName) $ specXducers ?spec

collectVars :: (?spec::Spec) => Path -> Transducer -> [XVar]
collectVars p Transducer{..} = 
    case txBody of
         Left is       -> concatMap (\i -> collectVars (p++[tiInstName i]) (getXducer $ tiTxName i)) is
         Right (_, vs) -> map (XVar p) vs

collectTypes :: (?spec::Spec) => Transducer -> Doc
collectTypes x = vcat $ stenum:(map mkType $ foldl' add [] $ collectTypes' x)
    where add :: [(Type, [String])] -> Type -> [(Type, [String])]
          add []      t = [(t,[])]
          add ((t0,as):ts) t = case (t0,t) of
                                    (Struct _ fs1, Struct (Just n2) fs2) -> if' (fs1 == fs2) ((t0,n2:as):ts) ((t0,as):(add ts t))
                                    _                                    -> (t0,as):(add ts t)
          -- state enum
          stenum = case txBody x of
                        Left _        -> empty
                        Right (cfa,_) -> mkEnumType n $ map (stateName x) locs
                                         where locs = cfaDelayLocs cfa `delete` cfaInitLoc 
                                               n = stateTypeName x


collectTypes' :: (?spec::Spec) => Transducer -> [Type]
collectTypes' Transducer{..} = 
    case txBody of
         Left _         -> []
         Right (_, vs) -> nub $ (concatMap (collectTypesT . varType) vs) ++ 
                                (collectTypesT txOutType) ++ 
                                (concatMap (collectTypesT . fst) txInput)

-- Bools and bitvectors are builtins in Boogie - ignore them.
-- Strip sequence types.
collectTypesT :: (?spec::Spec) => Type -> [Type]
collectTypesT t@(Enum _)      = [t]
collectTypesT t@(Struct fs)   = nub $ t:(map (\(Field _ t) -> collectTypesT t) fs)
collectTypesT    (Ptr _)      = error "Pointer type in transducer"
collectTypesT    (Seq t)      = collectTypesT t         
collectTypesT  t@(Array t' _) = nub $ t:(collectTypesT t')
collectTypesT    (VarArray _) = error "VarArray type in transducer"
collectTypesT    _            = []

mkVar :: (?spec::Spec) => XVar -> Doc
mkVar (XVar p v) = text "var" <+> xvName p (varName v) <+> char ':' <+> (typeName $ varType v)

typeName :: Type -> Doc
typeName (Bool _)            = text "bool"
typeName (SInt _ _)          = error "Not implemented: signed bitvectors in Spec2Boogie.hs"
typeName (UInt _ w)          = text $ "bv" ++ show w
typeName (Enum _ e)          = text e
typeName (Struct Nothing _)  = error "Not implemented: anonymous struct in Spec2Boogie.hs"
typeName (Struct (Just n) _) = text n
typeName (Array _ _ _)       = error "Not implemented: arrays in Spec2Boogie.hs"


mkEnumType :: [String] -> Doc
mkEnumType n es = (text "type" <+> text "finite" <+> text n <> semi)
                  $$
                  (vcat $ map (\e -> text "const" <+> text "unique" <+> text e <> colon <+> text n <> semi) es)
                  $$
                  (text "axiom" <+> parens (text "forall" <+> text "_x" <> colon <+> text n <> text "::" <+> disj) <> semi)
    where disj = hcat $ punctuate (text "||") $ map (\e -> text "_x" <+> text "==" <+> text e) es

mkType :: (?spec::Spec) => Type -> [String] -> Doc
mkType (Enum   _ n)  _ = mkEnumType n es
    where Enumeration _ es = getEnumeration n 
mkType (Struct n fs) as = (text "type" <+> text "{:datatype}" <+> text n <> semi)
                          $$
                          (text "function" <+> text "{:constructor}" <+> text n <> parens args) <+> colon <+> name n <> semi
                          $$
                          (vcat $ map (\a -> text "type" <+> text a <+> char '=' <+> text n <> semi) as)
    where args = hsep
                 $ punctuate comma
                 $ map (\(Field nm t) -> text nm <> colon <> typeName t)
                 $ filter (not . isSeq) fs

mkXducer :: (?spec::Spec) => Path -> Transducer -> [(Path, String)] -> Doc
mkXducer p x@Transducer{..} fanout =
    case txBody of
         -- composite transducer
         Left is -> -- print instances; route each instance output to other instance inputs or to the top-level output
                    vcat $ punctuate (text "") 
                    $ (mapIdx (\i id -> mkXducer (p++[tiInstName i]) (getXducer $ tiTxName i) (connect id)) is)
                    where -- compute list of ports that an instance is connected to
                          connect :: Int -> [Path]
                          connect id | id == length is - 1 = fanout ++ ports
                                     | otherwise           = ports
                                     where 
                                     name = tiInputs $ is !! id
                                     ports = concatMap (\TxInstance{..} -> map (\(_,port) -> (p++[tiInstName], port)) 
                                                                           $ filter ((== name) . fst) 
                                                                           $ zip tiInputs (txInput $ getXducer tiTxName)) is
         -- simple transducer
         Right (_,vs) -> let spec = ?spec in
                         let ?spec = spec {specVar = vs} in
                         mkXducer' p x fanout
         

call :: Doc -> [Doc] -> Doc
call f args = text "call" <+> f <+> (parens $ hsep $ punctuate comma args) <> semi

assign :: Doc -> Doc -> Doc
assign l r = l <+> text ":=" <+> r <> semi


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
    symbols' _                        = []

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

    ([initst], states') = partition (null . fromJust . snd) $ filter isJust states
    -- transition CFAs
    initCFA = cfaLocTransCFA cfa initst
    cfas = M.fromList
           $ map (\ss -> (fromJust $ snd $ head ss, map ((\l -> (l, cfaLocTransCFA cfa l)) . fst) ss))
           $ sortAndGroup snd states'

    -- generate state var
    stvar = text "var" <+> stateVarName p <+> char ':' <+> stateTypeName x

    -- generate variables to store input and output symbols

    invars  = map mkSymVar insymbols
    outvars = map mkSymVar outsymbols

    vars = vcat $ stvar : text "" : invars : text "" : outvars

    mkSymVar :: Symbol -> Doc
    mkSymVar s = (text "var" <+> symVarName p s <+> char ':' <+> (typeName $ symbolType s) <> semi)
                 $+$
                 (text "var" <+> eoiVarName p s <+> char ':' <+> text "bool" <> semi)

    -- init method
    initproc = (text "procedure" <+> initializerName p <+> (parens empty)) $+$ lbrace $+$ (nest' $ mkCFA initCFA initst) $+$ rbrace

    -- input handlers
    handlers = map mkHandler insymbols

    mkHandler :: Symbol -> Doc
    mkHandler sym = sig $+$ lbrace $+$ nest' body $+$ rbrace
        where
        -- procedure signature
        sig =  text "procedure" <+> handlerName p sym 
           <+> (parens $ symVarName [] sym <> colon <> (typeName $ symbolType sym) <>
                         comma <+> text "eoi" <> colon <> text "bool")
        -- save input symbol and eof flag
        readinp = assign (symVarName p sym) (symVarName [] sym)
                  $+$
                  assign (eoiVarName p sym) (text "eoi")

        -- for each state where sym is handled, generate code from CFA
        handlers = maybe [] 
                         (\(loc, cfa) -> (stateVarName p <+> text "==" <+> stateName x loc, mkCFA cfa loc)) 
                         (M.lookup sym cfas)

        -- generate empty handlers (loop transitions) for all states where sym's parent is handled
        parents = init $ tail $ inits sym
        parentlocs = concatMap (\sym' -> maybe [] fst $ M.lookup sym' cfas) parents
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

    mkCFA :: CFA -> Loc -> Doc
    mkCFA cfa loc = mkCFA' cfa loc Nothing

    mkCFA' :: CFA -> Loc -> Maybe Loc -> Doc
    mkCFA' cfa from mto | Just from == mto  = empty                                        -- stop at the "to" node
                        | null trans        = assign (stateVarName p) (stateName x from) -- final location
                        | null (tail trans) = mkTransition lab0 $+$ mkCFA' cfa loc0 mto    -- single successor
                        | otherwise         = (mkSwitch 
                                               $ map (\(tlab,loc) -> (text "*", mkTransition tlab $+$ mkCFA' cfa loc pdom)) trans)
                                              $+$
                                              mkCFA' cfa pdom mto 
        where trans@((lab0,loc0):_) = cfaSuc from cfa
              -- postdominator of from
              pdom = case G.ipdom (from, cfa) of
                          [x] -> Just x
                          _   -> Nothing

    mkTransition :: TranLabel -> Doc
    mkTransition (TranStat (SAssume e))   = text "assume" <> (parens $ mkExpr e) <> semi
    mkTransition (TranStat (SAssign l r)) = assign (mkExpr l) (mkExpr r)
    mkTransition (TranStat (SAdvance e))  = mkAdvance e
    mkTransition TranNop                  = empty

    mkAdvance :: Expr -> Doc
    mkAdvance exp = eoi $+$ out $+$ randomize
        where sym = expr2Sym exp
              -- recursively output eoi to all children and reset their eoi var's to false
              eoi = map (\sym' -> output sym' True $+$ (assign (eoiVarName p sym') (text "false"))) 
                    $ init $ symbols' (symbolType sym) sym
              -- output current symbol value
              out = output sym False
              output s e = vcat 
                           $ map (\(path,port) -> call (handlerName path (port:tail s)) [symVarName p s, text $ if' e "true" "false"])
                           $ fanout
              -- randomize it
              randomize = text "havoc" <+> (parens $ symVarName p sym) <> semi

    mkExpr :: Expr -> Doc
    mkExpr (ESeqVal e)             = symVarName p $ expr2Sym e
    mkExpr (EVar v)                = xvName p v
    mkExpr (EConst v)              = mkConst v
    mkExpr (EField e f)            = text f <> char '#' <> mkExpr e
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
    mkExpr (EEOI e)                = parens $ (eoiVarName p $ expr2Sym e) <+> text "==" <+> text "true"

    bvbop op e1 e2 = text ("BV"++(show $ exprWidth e1)++op) <> (parens $ mkExpr e1 <> comma <+> mkExpr e2)

eoiVarName :: Path -> Symbol -> Doc
eoiVarName p s = pp p <> char '$' <> pp s <> text "_eoi"

symVarName :: Path -> Symbol -> Doc
symVarName p s = pp p <> char '$' <> pp s

handlerName :: Path -> Symbol -> Doc
handlerName p s = pp p <> char '$' <> text "handle_" <> pp s

stateVarName :: Path -> Doc
stateVarName p = pp p <> text "$$state"

stateName :: Transducer -> Loc -> Doc
stateName x l = (text $ txName x) <> text "$$" <> pp l

stateTypeName :: Transducer -> Doc
stateTypeName x = (text $ txName x) <> "_state_t"

initializerName :: Path -> Doc 
initializerName p = pp p <> text "$$init"
