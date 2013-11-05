module IRelation(Relation(..)) where

import IType
import IExpr
import CFA

data Relation = Relation { relName  :: String
                         , relArgs  :: [(String, Type)]
                         , relRules :: [CFA]
                         }
