{-# LANGUAGE ImplicitParams, TupleSections, RecordWildCards #-}

module Frontend.TransducerValidate(validateTxNS,validateTxImplementation2) where

import Data.List
import Control.Monad.Error
import Data.Maybe

import Util hiding (name)
import Pos
import Name
import TSLUtil
import Frontend.Spec
import Frontend.NS
import Frontend.Transducer
import Frontend.TransducerOps
import Frontend.Statement
import Frontend.StatementValidate
import Frontend.TypeOps
import Frontend.TVarOps
import Frontend.Type

validateTxNS :: (?spec::Spec, MonadError String me) => Transducer -> me ()
validateTxNS t = do
    let ns = txLocalDecls t
    uniqNames (\n -> "Identifier " ++ n ++ " declared multiple times in transducer " ++ sname t) ns
    case mapMaybe (\o -> fmap (o,) $ find (\o' -> name o' == name o) specNamespace) ns of
         []       -> return ()
         (o,o'):_ -> err (pos o) $ "Identifier " ++ sname o ++ " conflicts with global declaration at " ++ spos o'

validateTxImplementation2 :: (?spec::Spec, MonadError String me) => Transducer -> me ()
validateTxImplementation2 t = do
    case txBody t of
         Left is -> validateTxConnections t
         Right s -> validateTxStatement t

validateTxConnections :: (?spec::Spec, MonadError String me) => Transducer -> me ()
validateTxConnections tx@Transducer{txBody=Left is} = do
    let otype = Type ScopeTop $ txOutType tx
    -- every instance input refers to another local instance or global input of 
    -- the matching type
    mapIdxM_ (\inst iid -> do
        let x = getTransducer (tiTxName inst)
            xtype = Type ScopeTop $ txOutType x
        mapIdxM (\i id -> do let t = Type ScopeTop $ tspec $ txInput x !! id
                                 ptypes = (map (\i' -> (sname i', Type ScopeTop $ txOutType $ getTransducer $ tiTxName i')) is)
                                       ++ (map (\i' -> (sname i', Type ScopeTop $ tspec i')) $ txInput tx)
                             assert (elem (sname i) $ map fst ptypes) (pos i) 
                                    $ "Input stream name " ++ sname i ++ " does not refer to a transducer instance or input port"
                             let t' = fromJust $ lookup (sname i) ptypes
                             assert (typeIso t t') (pos i) 
                                    $ "Expected type " ++ (show $ tspec t) ++ " but " ++ sname i ++ " has type " ++ (show $ tspec t'))
                $ tiInputs inst
        -- the last transducer matches the output type of the composition
        when (iid == length is - 1) 
             $ assert (typeIso otype xtype) (pos inst) 
             $ "Expected output type " ++ (show $ tspec otype) ++ " but " ++ sname inst ++ " has output type " ++ (show $ tspec xtype))
        is


    -- TODO: no circular connections

validateTxStatement :: (?spec::Spec, MonadError String me) => Transducer -> me ()
validateTxStatement t@Transducer{txBody=Right s,..} = do
    let ?privoverride = False
    let ?scope = ScopeTransducer t
    validateStat' False s
    -- No sequences in local variables
    mapM_ (\v -> assert (not $ isSeqContainer $ varType v) (pos v) $ "Local variable of a transducer must not be (or contain) a sequence")
          $ stmtVar s
