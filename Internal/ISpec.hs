{-# LANGUAGE RecordWildCards, ImplicitParams, TupleSections #-}

module Internal.ISpec(Spec(..),
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
             typeWidth,
             enumToInt) where

import Data.List
import Data.Maybe
import Data.Tuple.Select
import qualified Data.Map as M
import qualified Data.Graph.Inductive.Graph as G
import Text.PrettyPrint

import TSLUtil
import Pos
import Util
import Internal.CFA
import Internal.IVar
import Internal.IType
import Internal.IExpr
import Internal.IRelation
import Internal.TranSpec
import PP
import Internal.PID
import qualified Frontend.NS as F

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
    pp spec@Spec{..} = (text $ "/* state variables: " ++ (show $ length sv) ++ "(" ++ show sbits ++ "bits), " ++ 
                               "label variables: "++ (show $ length lv) ++ "(" ++ show lbits ++ "bits)*/" )
                       $+$
                       (vcat $ map (($+$ text "") . pp) specEnum)
                       $+$
                       (vcat $ map (($+$ text "") . pp) specVar)
                       $+$
                       pp specTran 
                       where (sv,lv) = partition ((==VarState) . varCat) specVar 
                             sbits = let ?spec = spec in sum $ map typeWidth sv
                             lbits = let ?spec = spec in sum $ map typeWidth lv

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


twidth :: (?spec::Spec) => Type -> Int
twidth Bool        = 1
twidth (Ptr _)     = 64
twidth (SInt w)    = w
twidth (UInt w)    = w
twidth (Enum e)    = bitWidth $ length (enumEnums $ getEnumeration e) - 1
twidth (Array t l) = l * twidth t
twidth (Struct fs) = sum $ map typeWidth fs
twidth t           = error $ "twidth " ++ show t ++ " undefined"

typeWidth :: (?spec::Spec, Typed a) => a -> Int
typeWidth = twidth . typ


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

specAllMBs :: Spec -> [Pos]
specAllMBs spec = nub
                  $ map sel1
                  $ concatMap (\(pid, proc) -> map (\(loc, lab) -> (pos $ locAct lab, pid, loc)) $ filter (isMBLabel . snd) $ G.labNodes $ procCFA proc)
                  $ specAllProcs spec

specLookupMB :: Spec -> Pos -> [(PrID, Loc, F.Scope)]
specLookupMB spec p = 
    concat
    $ (\xs -> if' (length xs > 1) (error $ "specLookupMB: MB " ++ show p ++ " is instantiated in multiple processes") xs)
    $ filter (not . null)
    $ map (\(pid, proc) -> map (\(loc, lab) -> (pid, loc, fScope $ head $ locStack lab))
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
