module IRelation(Relation(..),
                 Apply(..)) where

import IType
import IExpr

data Relation = Relation { relName  :: String
                         , relArgs  :: [(String, Type)]
                         , relRules :: [Expr]
                         }

data Apply = Apply { applyRel  :: String
                   , applyArgs :: [Expr]
                   }
