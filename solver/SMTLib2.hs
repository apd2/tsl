-- Interface to SMT2 format

module SMT2Lib() where

import Text.PrettyPrint
import Text.Parsec
import qualified Text.Parsec.Token as T
import System.IO.Unsafe
import System.Process
import Control.Monad.Error

import BFormula
import ISpec
import IVar
import IType

data SMT2Config = SMT2Config {
    s2Solver :: String,  -- Name of the solver executable
    s2Opts   :: [String] -- Arguments passed on every invocation of the solver
}

------------------------------------------------------
-- Printing formulas in SMTLib2 format
------------------------------------------------------

class SMTPP a where
    smtpp :: a -> Doc

instance (?spec::Spec) => SMTPP [Formula] where
    smtpp fs = -- variable declarations
               vcat
               $ map smptpp 
               $ S.fromList $ S.toList 
               $ concatMap fVar fs
               $+$
               vcat
               $ map smtpp fs

instance (?spec::Spec) => SMTPP Var where
    smtpp v = parens $  text "declare-fun" 
                    <+> (char '|' <> varName v <> char '|') 
                    <+> text "()" 
                    <+> smtpp (varType v)

instance (?spec::Spec) => SMTPP Type where
    smtpp Bool            = text "Bool"
    smtpp (SInt w)        = parens $ char '_' <+> text "BitVec" <+> int w
    smtpp (UInt w)        = parens $ char '_' <+> text "BitVec" <+> int w
    smtpp (Enum n)        = text n
    smtpp (Struct [Field])
          | Ptr      Type
          | Array    Type Int


instance (?spec::Spec) => SMTPP Formula where

------------------------------------------------------
-- Parsing solver output
------------------------------------------------------

lexer  = T.makeTokenParser emptyDef

symbol  = T.symbol  lexer
decimal = T.decimal lexer

satres = ((Just False) <$> symbol "unsat") <|> 
         ((Just True)  <$> symbol "sat")

unsatcore = option [] (parens $ many $ decimal)

------------------------------------------------------
-- Running solver in different modes
------------------------------------------------------

runSolver :: SMT2Config -> Doc -> Parsec String () a -> a
runSolver cfg spec parser = 
    let (retcode, out, err) = unsafePerformIO $ readProcessWithExitCode (s2Solver cfg) (s2Opts cfg) (show spec)
    if retcode == ExitSuccess 
       then case parse parser "" out of
                 Left e  -> error $ "Error parsing SMT solver output: " ++ e
                 Right x -> x
       else error $ "Error running SMT solver: " ++ err

checkSat :: SMT2Config -> [Formula] -> Maybe Bool
checkSat cfg fs = runSolver cfg spec satres
    where spec = smtpp fs 
              $$ text "(check-sat)"


getUnsatCore :: [Formula] -> Maybe [Int]
getUnsatCore =
    runSolver cfg spec
    $ ((\res core -> case res of
                          Just False -> Just core
                          _          -> Nothing)
       <$> satres <*> unsatcore)
    where spec = text "(set-option :produce-unsat-cores true)"
              $$ smtpp fs 
              $$ text "(check-sat)"
              $$ text "(get-unsat-core)"
