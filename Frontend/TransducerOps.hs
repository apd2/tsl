{-# LANGUAGE ImplicitParams #-}

module Frontend.TransducerOps(txLocalDecls) where

import Frontend.Spec
import Frontend.NS
import Frontend.Transducer
import Frontend.Statement

txLocalDecls :: (?spec::Spec) => Transducer -> [Obj]
txLocalDecls t = (ObjTxOutput t) : 
                 (map (ObjTxInput t) (txInput t))    ++
                 case txBody t of
                      Left is -> map (ObjTxInstance t) is
                      Right s -> map (ObjVar (ScopeTransducer t)) (stmtVar s)     
