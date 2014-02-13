module ACFA(ACFA, 
            acfaTraceFile,
            acfaAVars) where 

import qualified Data.Graph.Inductive as G
import qualified Data.Map             as M
import Data.List

import Predicate
import Cascade
import BFormula
import CFA
import TSLUtil
import IExpr

-- Abstract CFA - has the same topology as CFA, but labels transitions
-- with variable update functions and states--with sets of abstract
-- vars to be recomputed in this state and a map from abstract vars to
-- locations where these vars are recomputed
type ACFA = G.Gr ([(AbsVar, Expr)], M.Map AbsVar Loc) (Int,Maybe Formula,[MECascade])

acfaTraceFile :: ACFA -> String -> a -> a
acfaTraceFile acfa title = graphTraceFile (G.emap (\(num, mpre, upd) -> show num ++ ": " ++ (maybe "" show mpre)  ++ ": " ++ (show $ length upd)) acfa) title

acfaAVars :: ACFA -> [AbsVar]
acfaAVars = nub . concatMap (M.keys . snd . snd) . G.labNodes
