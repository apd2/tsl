{-# LANGUAGE ImplicitParams, FlexibleContexts, TupleSections #-}

module Frontend.Spec(Spec(Spec,specTemplate,specType,specConst,specTransducer), 
            emptySpec,
            mergeSpecs) where

import Data.List
import qualified Text.PrettyPrint as P

import PP
import Util hiding (name)
import Name
import Frontend.Type
import Frontend.Template
import Frontend.Const
import Frontend.Transducer

data Spec = Spec { specTemplate   :: [Template]
                 , specType       :: [TypeDecl]
                 , specConst      :: [Const]
                 , specTransducer :: [Transducer]
                 }

instance PP Spec where 
    pp (Spec tms ts cs txs) = (P.vcat $ map ((P.$+$ P.text "") . pp) ts)
                              P.$+$
                              (P.vcat $ map ((P.$+$ P.text "") . pp) cs)
                              P.$+$
                              (P.vcat $ map ((P.$+$ P.text "") . pp) tms)
                              P.$+$
                              (P.vcat $ map ((P.$+$ P.text "") . pp) txs)


instance Show Spec where
    show = P.render . pp

emptySpec = Spec [] [] []

mergeSpecs :: Spec -> Spec -> Spec
mergeSpecs (Spec tm1 t1 c1 tx1) (Spec tm2 t2 c2 tx2) = Spec tm (t1++t2) (c1++c2) (tx1++tx2)
    where tm = foldl' mergeTemplates tm1 tm2

-- If template with the same name exists in the list, merge the two;
-- otherwise, add template to the list
mergeTemplates :: [Template] -> Template -> [Template]
mergeTemplates tms tm = maybe (tms ++ [tm]) 
                              (\_ -> map (\tm' -> if' (sname tm' == sname tm) (mergeTemplate tm' tm) tm') tms)
                              $ find ((== sname tm)  . sname) tms
