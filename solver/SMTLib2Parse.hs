{-# LANGUAGE ImplicitParams #-}

module SMTLib2Parse (satresParser,
                     unsatcoreParser,
                     modelParser) where

import Data.Maybe
import Data.List
import Data.Bits
import qualified Data.Map             as M
import Text.Parsec hiding ((<|>))
import Text.Parsec.Language
import qualified Text.Parsec.Token    as T
import Control.Applicative hiding (many)
import Numeric

import Util
import ISpec
import IType
import IVar
import IExpr
import Store
import Predicate

data ModelDecl = DeclConst  {dconstName::String, dconstType::TypeSpec}
               | DeclVarAsn {dvarName::String, dvarVal::SMTExpr}
               deriving (Eq)

declIsConst :: ModelDecl -> Bool
declIsConst (DeclConst _ _) = True
declIsConst _               = False

declIsAsn :: ModelDecl -> Bool
declIsAsn (DeclVarAsn _ _) = True
declIsAsn _                = False

data TypeSpec = TypeName String
              | TypeBV   Int
              deriving (Eq)

data SMTExpr = ExpIdent String
             | ExpBool  Bool
             | ExpInt   Integer
             | ExpApply String [SMTExpr]
             deriving (Eq, Ord, Show)

------------------------------------------------------
-- exports
------------------------------------------------------

satresParser :: Parsec String () (Maybe Bool)
satresParser = ((Just False) <$ symbol "unsat") <|> 
               ((Just True)  <$ symbol "sat")

unsatcoreParser :: Parsec String () [Int]
unsatcoreParser = option [] (parens $ many $ (char 'a' *> (fromInteger <$> decimal)))

modelParser :: (?spec::Spec) => [(String, Term)] -> Parsec String () Store
modelParser ptrmap = storeFromModel ptrmap <$> model

------------------------------------------------------
-- Parsing solver output
------------------------------------------------------

reservedNames   = ["model", "declare-fun", "define-fun", "forall", "BitVec", "true", "false"]
reservedOpNames = ["_"]

lexer  = T.makeTokenParser emptyDef { T.identStart      = letter <|> char '_'
                                    , T.identLetter     = alphaNum <|> char '_' <|> char '-' <|> char '!'
                                    , T.commentLine     = ";;"
                                    , T.reservedNames   = reservedNames
                                    , T.reservedOpNames = reservedOpNames
                                    }

identifier = T.identifier lexer
symbol     = T.symbol     lexer
decimal    = T.decimal    lexer
parens     = T.parens     lexer
reserved   = T.reserved   lexer
operator   = T.operator   lexer
reservedOp = T.reservedOp lexer
lexeme     = T.lexeme     lexer

ident =  identifier 
     <|> char '|' *> (many $ noneOf ['|']) <* char '|'

model = catMaybes <$> (parens $ reserved "model" *> many model_decl)

model_decl :: Parsec String () (Maybe ModelDecl)
model_decl =  try const_decl
          <|> try var_asn
          <|> try forall

const_decl = parens $ (\n t -> Just $ DeclConst n t)    <$ reserved "declare-fun" <*> ident <* (parens spaces) <*> typespec
var_asn    = parens $ (\n _ e -> Just $ DeclVarAsn n e) <$ reserved "define-fun"  <*> ident <* (parens spaces) <*> typespec <*> expr
forall     = parens $ (\_ _ -> Nothing)                 <$ reserved "forall"      <*> args  <*> expr

args = parens $ (,) <$> many arg
arg  = parens $ (,) <$> ident <*> typespec

expr =  fapply
    <|> literal
    <|> (ExpIdent <$> ident)

fapply = parens $ ExpApply <$> fname <*> (many expr)
fname  =  ident 
      <|> operator

typespec =  TypeName <$> ident
        <|> bvtype

bvtype = parens $ (TypeBV . fromInteger) <$> (reservedOp "_" *> reserved "BitVec" *> decimal)

literal =  (ExpInt <$> decimal)
       <|> (ExpBool True <$ reserved "true")
       <|> (ExpBool False <$ reserved "false")
       <|> ((ExpInt . fst . head . readHex) <$> lexeme (char '#' *> char 'x' *> many1 hexDigit))

------------------------------------------------------
-- Compiling parsed data
------------------------------------------------------

storeFromModel :: (?spec::Spec) => [(String, Term)] -> [ModelDecl] -> Store
storeFromModel ptrmap decls = 
    let asndecls = map (\d -> (dvarName d, dvarVal d)) 
                 $ filter (\d -> declIsAsn d && not (isPrefixOf "addrof-" (dvarName d))) decls in
    let ?addrofmap = map (\(v,n) -> case lookup n ptrmap of
                                         Nothing -> error "storeFromModel: undefined constant"
                                         Just t  -> (v,t))
                     $ map ((\(DeclVarAsn n v) -> (v,n)) . head)
                     $ sortAndGroup dvarVal
                     $ filter (\d -> declIsAsn d && isPrefixOf "addrof-" (dvarName d)) decls in
    storeUnions $ map storeFromAsn asndecls

storeFromAsn :: (?spec::Spec, ?addrofmap::[(SMTExpr, Term)]) => (String, SMTExpr) -> Store
storeFromAsn (n, e) = SStruct $ M.singleton (varName var) val
    where var = getVar n
          val = storeFromExpr (varType var) e

storeFromExpr :: (?spec::Spec, ?addrofmap::[(SMTExpr, Term)]) => Type -> SMTExpr -> Store
storeFromExpr t e = case lookup e ?addrofmap of
                         Nothing   -> storeFromExpr' t e
                         Just term -> SVal $ PtrVal $ evalLExpr $ termToExpr term

storeFromExpr' :: (?spec::Spec, ?addrofmap::[(SMTExpr, Term)]) => Type -> SMTExpr -> Store
storeFromExpr' t (ExpIdent i) = if' (typ v /= t) (error "storeFromExpr: identifier type mismatch") $ 
                                (SVal v)
    where v = valFromIdent i
storeFromExpr' t (ExpBool b) = if' (t /= Bool) (error "storeFromExpr: bool type mismatch") $ 
                               (SVal $ BoolVal b)
storeFromExpr' (UInt w) (ExpInt v) = SVal $ UIntVal w v
storeFromExpr' (SInt w) (ExpInt v) | msb v == w - 1 = 
    SVal $ SIntVal w $ - ((foldl' complementBit v [0..w-1]) + 1)
                                   | otherwise      = SVal $ SIntVal w v
storeFromExpr' (Struct fs) (ExpApply f as) | length fs /= length as = error "storeFromExpr: incorrect number of fields in a struct"
                                           | otherwise = 
    SStruct $ M.fromList $ map (\((Field n t), e) -> (n, storeFromExpr t e)) $ zip fs as
storeFromExpr' t e = error $ "storeFromExp " ++ show t ++ " " ++ show e

valFromIdent :: (?spec::Spec) => String -> Val
valFromIdent i = case lookupEnumerator i of
                      Just _  -> EnumVal i
                      Nothing -> error $ "valFromIdent: unknown enumerator: " ++ show i
