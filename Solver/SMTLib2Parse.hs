{-# LANGUAGE ImplicitParams #-}

module Solver.SMTLib2Parse (assertName,
                     satresParser,
                     unsatcoreParser,
                     modelParser,
                     errorParser) where

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
import TSLUtil
import Internal.ISpec
import Internal.IType
import Internal.IVar
import Internal.IExpr
import Solver.Store
import Abstract.Predicate

-- appended to each assertion name
assertName = "__assert"

data ModelDecl = DeclConst  {dconstName::String, dconstType::TypeSpec}
               | DeclVarAsn {dvarName::String, dvarArgs::[String], dvarVal::SMTExpr}
               deriving (Eq)

declIsConst :: ModelDecl -> Bool
declIsConst (DeclConst _ _) = True
declIsConst _               = False

declIsAsn :: ModelDecl -> Bool
declIsAsn (DeclVarAsn _ _ _) = True
declIsAsn _                  = False

data TypeSpec = TypeName  String
              | TypeArray TypeSpec TypeSpec                
              | TypeBV    Int
              deriving (Eq)

data SMTExpr = ExpIdent   String
             | ExpBool    Bool
             | ExpInt     Integer
             | ExpApply   String [SMTExpr]
             | ExpAsArray String
             deriving (Eq, Ord, Show)

------------------------------------------------------
-- exports
------------------------------------------------------

satresParser :: Parsec String () (Maybe Bool)
satresParser = ((Just False) <$ symbol "unsat") <|> 
               ((Just True)  <$ symbol "sat")

unsatcoreParser :: Parsec String () [Int]
unsatcoreParser = option [] (parens $ many $ (string assertName *> (fromInteger <$> decimal)) <* spaces)

modelParser :: (?spec::Spec) => [(String, Term)] -> Parsec String () Store
modelParser ptrmap = storeFromModel ptrmap <$> model

errorParser = char '(' *> symbol "error" *> (many $ noneOf ['(',')']) <* char ')' <* spaces
------------------------------------------------------
-- Parsing solver output
------------------------------------------------------

reservedNames   = ["model", "declare-fun", "define-fun", "forall", "BitVec", "Array", "true", "false", "as-array"]
reservedOpNames = ["_"]

lexer  = T.makeTokenParser emptyDef { T.identStart      =  letter 
                                                       <|> char '_' 
                                                       <|> char '$'
                                    , T.identLetter     =  alphaNum 
                                                       <|> char '_' 
                                                       <|> char '-' 
                                                       <|> char '!' 
                                                       <|> char '$' 
                                                       <|> char '/'
                                                       <|> char ':'
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
     <|> char '|' *> (many $ noneOf ['|']) <* char '|' <* spaces

model = catMaybes <$> (parens $ reserved "model" *> many model_decl)

model_decl :: Parsec String () (Maybe ModelDecl)
model_decl =  try const_decl
          <|> try var_asn
          <|> try forall

const_decl = parens $ (\n t -> Just $ DeclConst n t)    <$ reserved "declare-fun" <*> ident <* (parens spaces) <*> typespec
var_asn    = parens $ (\n as _ e -> if' (isPrefixOf assertName n) Nothing (Just $ DeclVarAsn n as e)) -- ignore assignments to assertions
                                                        <$ reserved "define-fun"  <*> ident <*> args <*> typespec <*> expr
forall     = parens $ (\_ _ -> Nothing)                 <$ reserved "forall"      <*> args  <*> expr

args = parens $ many arg
arg  = parens $ ident <* typespec

expr =  (isarray *> asarray)
    <|> fapply
    <|> literal
    <|> (ExpIdent <$> ident)

asarray = parens $ ExpAsArray <$> (reservedOp "_" *> reserved "as-array" *> ident)
isarray = try $ lookAhead asarray

fapply = parens $ ExpApply <$> fname <*> (many expr)
fname  =  ident 
      <|> operator

typespec =  (parens $  (TypeArray <$ reserved "Array" <*> typespec <*> typespec)
                   <|> ((TypeBV . fromInteger) <$> (reservedOp "_" *> reserved "BitVec" *> decimal)))
        <|> TypeName <$> ident

literal =  (ExpInt <$> decimal)
       <|> (ExpBool True <$ reserved "true")
       <|> (ExpBool False <$ reserved "false")
       <|> (try $ lexeme $ string "#x" *> ((ExpInt . fst . head . readHex) <$> many1 hexDigit))
       <|> (try $ lexeme $ string "#b" *> ((ExpInt . readBin)              <$> (many1 $ char '0' <|> char '1')))

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
                     $ map ((\(DeclVarAsn n _ v) -> (v,n)) . head)
                     $ sortAndGroup dvarVal
                     $ filter (\d -> declIsAsn d && isPrefixOf "addrof-" (dvarName d)) decls 
        ?alldecls = decls in
    storeUnions ?spec (mapMaybe storeFromAsn asndecls)

storeFromAsn :: (?spec::Spec, ?addrofmap::[(SMTExpr, Term)], ?alldecls::[ModelDecl]) => (String, SMTExpr) -> Maybe Store
storeFromAsn (n, e) = fmap (\var -> let val = storeFromExpr (varType var) e M.empty in
                                    SStruct (M.singleton (varName var) val) ?spec)
                           $ lookupVar n

storeFromExpr :: (?spec::Spec, ?addrofmap::[(SMTExpr, Term)], ?alldecls::[ModelDecl]) => Type -> SMTExpr -> M.Map String SMTExpr -> Store
storeFromExpr t e args = case lookup e ?addrofmap of
                              Nothing   -> storeFromExpr' t e args
                              Just term -> SVal $ PtrVal $ evalLExpr $ termToExpr term

storeFromExpr' :: (?spec::Spec, ?addrofmap::[(SMTExpr, Term)], ?alldecls::[ModelDecl]) => Type -> SMTExpr -> M.Map String SMTExpr -> Store
storeFromExpr' t (ExpIdent i) args = 
    case lookupEnumerator i of
         Just _  -> SVal $ EnumVal i
         Nothing -> case M.lookup i args of
                         Just e  -> storeFromExpr t e M.empty
                         Nothing -> error $ "storeFromExpr: unknown enumerator: " ++ show i
storeFromExpr' t (ExpBool b) _ = if' (not $ isBool t) (error "storeFromExpr: bool type mismatch") $ 
                                     (SVal $ BoolVal b)
storeFromExpr' (UInt _ w) (ExpInt v) _ = SVal $ UIntVal w v
storeFromExpr' (SInt _ w) (ExpInt v) _ | msb v == w - 1 = 
    SVal $ SIntVal w $ - ((foldl' complementBit v [0..w-1]) + 1)
                                       | otherwise      = SVal $ SIntVal w v
storeFromExpr' t (ExpApply "=" [a1,a2]) args = SVal $ BoolVal $ v1 == v2
    where -- XXX: assume that comparisons are always between (integer) array indices
          SVal (UIntVal _ v1) = storeFromExpr (UInt Nothing 32) a1 args
          SVal (UIntVal _ v2) = storeFromExpr (UInt Nothing 32) a2 args
storeFromExpr' t (ExpApply "ite" [i,th,el]) args = if' cond (storeFromExpr' t th args) (storeFromExpr' t el args)
    where cond = case storeFromExpr (Bool Nothing) i args of
                      SVal (BoolVal b) -> b
                      _                -> error $ "storeFromExpr: cannot evaluate boolean expression " ++ show i
storeFromExpr' (Struct _ fs) (ExpApply n as) args | isPrefixOf "mk-Struct" n =
    if length fs /= length as 
       then error "storeFromExpr: incorrect number of fields in a struct"
       else SStruct (M.fromList $ map (\((Field n t), e) -> (n, storeFromExpr t e args)) $ zip fs as) ?spec
storeFromExpr' (Array _ t l) (ExpAsArray n) _ | isNothing marr = error $ "storeFromExpr: array \"" ++ n ++ "\" not found"
                                            | otherwise      = SArr $ M.fromList $ map (\i -> (i, storeFromExpr t e $ M.singleton a (ExpInt $ fromIntegral i))) [0..l-1]
    where marr = find ((==n) . dvarName) ?alldecls
          Just (DeclVarAsn _ [a] e) = marr
storeFromExpr' t e _ = error $ "storeFromExp " ++ show t ++ " " ++ show e
