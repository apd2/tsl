{-# LANGUAGE RecordWildCards, ImplicitParams, TupleSections #-}

module ISpec(Spec(..),
             Process(..),
             specTmpVar,
             specStateVar,
             specGetProcess,
             specAllCFAs,
             specAllProcs,
             specAllMBs,
             specLookupMB,
             specGetCFA,
             specMapCFA,
             specInlineWirePrefix,
             cfaLocInlineWirePrefix,
             lookupVar,
             getVar,
             getRelation,
             lookupEnumerator,
             getEnumerator,
             getEnumeration,
             enumToInt) where

import Data.List
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Graph.Inductive.Graph as G
import Text.PrettyPrint

import Pos
import Util
import CFA
import IVar
import IType
import IExpr
import IRelation
import TranSpec
import PP
import PID
import qualified NS as F

data Process = Process {
    procName     :: String,
    procCFA      :: CFA,
    procChildren :: [Process]
}

data Spec = Spec {
    specEnum   :: [Enumeration],
    specVar    :: [Var],
    specWire   :: Maybe CFA,                   -- wire assignment
    specPrefix :: Maybe CFA,                   -- prefix blocks
    specProc   :: [Process],                   -- processes
    specCAct   :: CFA,                         -- controllable transitions
    specUpds   :: M.Map String [(Expr, Expr)], -- variable update functions specified explicitly
    specRels   :: [Relation],
    specApply  :: [Apply],
    specTran   :: TranSpec                     -- info required for variable update
                                               -- computation
}

specStateVar :: Spec -> [Var]
specStateVar = filter ((==VarState) . varCat) . specVar

specTmpVar :: Spec -> [Var]
specTmpVar = filter ((==VarTmp) . varCat) . specVar

instance PP Spec where
    pp Spec{..} = (text $ "/* state variables: " ++ (show $ length sv) ++ "(" ++ show sbits ++ "bits), " ++ 
                          "label variables: "++ (show $ length lv) ++ "(" ++ show lbits ++ "bits)*/" )
                  $+$
                  (vcat $ map (($+$ text "") . pp) specEnum)
                  $+$
                  (vcat $ map (($+$ text "") . pp) specVar)
                  $+$
                  pp specTran 
                  where (sv,lv) = partition ((==VarState) . varCat) specVar 
                        sbits = sum $ map typeWidth sv
                        lbits = sum $ map typeWidth lv

lookupVar :: (?spec::Spec) => String -> Maybe Var
lookupVar n = find ((==n) . varName) $ specVar ?spec 

getVar :: (?spec::Spec) => String -> Var
getVar n = fromJustMsg ("getVar: variable " ++ n ++ " not found") $ lookupVar n

lookupEnumerator :: (?spec::Spec) => String -> Maybe Enumeration
lookupEnumerator e = find (elem e . enumEnums) $ specEnum ?spec

getEnumerator :: (?spec::Spec) => String -> Enumeration
getEnumerator e = fromJustMsg ("getEnumerator: enumerator " ++ e ++ " not found") $ lookupEnumerator e

getEnumeration :: (?spec::Spec) => String -> Enumeration
getEnumeration e = fromJustMsg ("getEnumeration: enumeration " ++ e ++ " not found")
                   $ find ((==e) . enumName) $ specEnum ?spec

getRelation :: (?spec::Spec) => String -> Relation
getRelation r = fromJustMsg ("getRelation: relation " ++ r ++ " not found")
                $ find ((==r) . relName) $ specRels ?spec

-- Get sequence number of an enumerator
enumToInt :: (?spec::Spec) => String -> Int
enumToInt n = fst $ fromJust $ find ((==n) . snd) $ zip [0..] (enumEnums $ getEnumerator n)

specGetProcess :: Spec -> PrID -> Process
specGetProcess spec (PrID n names) | names == [] = root
                                   | otherwise   = specGetProcess' root names
    where root = fromJustMsg ("specGetProcess " ++ n ++ ": error") $ find ((== n) . procName) $ specProc spec

specGetProcess' :: Process -> [String] -> Process
specGetProcess' proc (n:names) | names == [] = child
                               | otherwise   = specGetProcess' child names
    where child = fromJustMsg "specGetProcess': error" $ find ((== n) . procName) $ procChildren proc

specGetCFA :: Spec -> EPID -> CFA
specGetCFA spec (EPIDProc pid) = procCFA $ specGetProcess spec pid
specGetCFA spec EPIDCont       = specCAct spec 

specAllCFAs :: Spec -> [(EPID, CFA)]
specAllCFAs Spec{..} = concatMap (\p -> procAllCFAs (PrID (procName p) []) p) specProc  ++
                       [(EPIDCont, specCAct)]

specAllMBs :: Spec -> [(Pos, PrID, Loc)]
specAllMBs spec = concatMap (\(pid, proc) -> map (\(loc, lab) -> (pos $ locAct lab, pid, loc)) $ filter (isMBLabel . snd) $ G.labNodes $ procCFA proc)
                  $ specAllProcs spec

specLookupMB :: Spec -> Pos -> Maybe (PrID, Loc, F.Scope)
specLookupMB spec p = listToMaybe
    $ concatMap (\(pid, proc) -> map (\(loc, lab) -> (pid, loc, fScope $ head $ locStack lab))
                                 $ (\xs -> if' (length xs > 1) (error "specLookupMB: multiple instantiations of the same MB") xs)
                                 $ filter ((== p) . pos . locAct . snd)
                                 $ filter (isMBLabel . snd) 
                                 $ G.labNodes $ procCFA proc)
    $ specAllProcs spec


procAllCFAs :: PrID -> Process -> [(EPID, CFA)]
procAllCFAs pid proc = (EPIDProc pid, procCFA proc) :
                       concatMap (\p -> procAllCFAs (childPID pid (procName p)) p) (procChildren proc) 

specAllProcs :: Spec -> [(PrID, Process)]
specAllProcs Spec{..} = concatMap (\p -> procAllForkedProcs (PrID (procName p) []) p) specProc

procAllForkedProcs :: PrID -> Process -> [(PrID, Process)]
procAllForkedProcs pid p = (pid,p) : (concatMap (\p' -> procAllForkedProcs (childPID pid (procName p')) p') $ procChildren p)

-- Apply transformation to all CFA's in the spec
specMapCFA :: (CFA -> CFA) -> Spec -> Spec
specMapCFA f spec = 
   spec { specProc = map (procMapCFA f) $ specProc spec
        , specCAct = f $ specCAct spec}

procMapCFA :: (CFA -> CFA) -> Process -> Process
procMapCFA f proc = 
    proc { procCFA      = f $ procCFA proc
         , procChildren = map (procMapCFA f) $ procChildren proc
         }

specInlineWirePrefix :: Spec -> Spec
specInlineWirePrefix spec = specMapCFA (cfaInlineWirePrefix spec) spec

cfaInlineWirePrefix :: Spec -> CFA -> CFA
cfaInlineWirePrefix spec cfa = foldl' (\cfa0 loc -> let cfa1 = case specPrefix spec of
                                                                    Nothing -> cfa0
                                                                    Just a  -> cfaLocInline cfa0 loc a
                                                    in case specWire spec of
                                                            Nothing -> cfa1
                                                            Just w  -> cfaLocInline cfa1 loc w) 
                                      cfa locs
    -- Find delay locations with outgoing transitions
    where locs = filter (\loc -> (isDelayLabel $ cfaLocLabel loc cfa) && (G.suc cfa loc /= []))
                        $ G.nodes cfa

cfaLocInlineWirePrefix :: Spec -> CFA -> Loc -> CFA
cfaLocInlineWirePrefix spec cfa loc =
    let cfa1 = case specPrefix spec of
                    Nothing -> cfa
                    Just a  -> cfaLocInline cfa loc a
               in case specWire spec of
                       Nothing -> cfa1
                       Just w  -> cfaLocInline cfa1 loc w
