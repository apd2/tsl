module ACFA(ACFA, 
            acfaTraceFile) where 

import qualified Data.Graph.Inductive as G
import qualified Data.Map             as M

import Predicate
import Cascade
import BFormula
import CFA
import TSLUtil

-- Abstract CFA - has the same topology as CFA, but labels transitions
-- with variable update functions and states--with sets of abstract
-- vars to be recomputed in this state and a map from abstract vars to
-- locations where these vars are recomputed
type ACFA = G.Gr ([AbsVar], M.Map AbsVar Loc) (Int,Maybe Formula,[ECascade])

acfaTraceFile :: ACFA -> String -> a -> a
acfaTraceFile acfa title = graphTraceFile (G.emap (\(id, mpre, upd) -> show id ++ ": " ++ (maybe "" show mpre)  ++ ": " ++ (show $ length upd)) acfa) title

