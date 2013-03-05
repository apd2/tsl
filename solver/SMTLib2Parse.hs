{-# LANGUAGE ImplicitParams #-}

module SMTLib2Parse () where

import Data.Maybe
import Text.Parsec
import Text.Parsec.Language
import qualified Text.Parsec.Token    as T

import ISpec
import Store

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
-- Parsing solver output
------------------------------------------------------

reserved    = ["model", "declare-fun", "define-fun", "forall", "BitVec", "true", "false"]
reservedOps = ["_"]

lexer  = T.makeTokenParser emptyDef { T.identStart      = letter <|> char '_'
                                    , T.identLetter     = alphaNum <|> char '_' <|> char '-' <|> char '!'
                                    , T.commentLine     = ";;"
                                    , T.reservedNames   = reserved
                                    , T.reservedOpNames = reservedOps
                                    }

lidentifier = T.identifier lexer
lsymbol     = T.symbol     lexer
ldecimal    = T.decimal    lexer
lparens     = T.parens     lexer
lreserved   = T.reserved   lexer
loperator   = T.operator   lexer
lreservedOp = T.reservedOp lexer
lexeme      = T.lexeme     lexer

ident =  lidentifier 
     <|> char '|' *> (many $ noneOf ['|']) <* char '|'

satres = ((Just False) <$ lsymbol "unsat") <|> 
         ((Just True)  <$ lsymbol "sat")

unsatcore :: Parsec String () [Int]
unsatcore = option [] (lparens $ many $ (char 'a' *> (fromInteger <$> ldecimal)))

model = catMaybes <$> lparens $ lreserved "model" *> many model_decl

model_decl =  const_decl
          <|> var_asn
          <|> forall

const_decl = (Just . (\n t   -> DeclConst  n t)) <$> lparens $ lreserved "declare-fun" *> ident <*> (lparens spaces) *> typespec
var_asn    = (Just . (\n _ e -> DeclVarAsn n e)) <$> lparens $ lreserved "define-fun"  *> ident <*> (lparens spaces) *> typespec <*> expr
forall     = (\_ _ -> Nothing)                   <$> lparens $ lreserved "forall"      *> args  <*> expr

args = lparens $ many arg
arg  = lparens $ ident <*> typespec

expr =  fapply
    <|> (ExpLit   <$> literal)
    <|> (ExpIdent <$> ident)

fapply = ExpApply <$> lparens $ fname <*> (many expr)
fname  =  ident 
      <|> loperator

typespec =  ident
        <|> bvtype

bvtype = parens $ lreservedOp "_" *> lreserved "BitVec" *> ldecimal

literal =  (ExpInt <$> ldecimal)
       <|> (ExpBool True <$ lreserved "true")
       <|> (ExpBool False <$ lreserved "false")
       <|> ((ExpInt . fst . head . readHex) <$> llexeme $ char '#' *> char 'x' *> many1 hexDigit)

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
storeFromAsn (name, e) = SStruct [(varName var, val)]
    where var = getVar name 
          val = storeFromExpr (varType var) e

storeFromExpr :: (?spec::Spec, ?addrofmap::[(SMTExpr, Term)]) => Type -> SMTExpr -> Store
storeFromExpr t e = case lookup e ?addrofmap of
                         Nothing -> storeFromExpr' t e
                         Just t  -> SVal $ PtrVal $ evalLExpr $ termToExpr t

storeFromExpr' :: (?spec::Spec, ?addrofmap::[(SMTExpr, Term)]) => Type -> SMTExpr -> Store
storeFromExpr' t (ExpIdent i) = if' (typ v /= t) (error "storeFromExpr: identifier type mismatch") $ 
                               (SVal $ Just v)
    where v = valFromIdent i
storeFromExpr' t (ExpBool b) = if' (typ v /= Bool) (error "storeFromExpr: bool type mismatch") $ 
                               (SVal $ Just $ BoolVal b)
storeFromExpr' (UInt w) (ExpIdent i) = SVal $ Just $ UIntVal w i
storeFromExpr' (SInt w) (ExpIdent i) | msb v == w - 1 = 
    SVal $ Just $ SIntVal w $ - ((foldl' (\v i -> complementBit v i) v [0..w-1]) + 1)
                                     | otherwise      = SVal $ Just $ SIntVal w i
storeFromExpr' (Struct fs) (ExpApply f as) | length fs /= length as = error "storeFromExpr: incorrect number of fields in a struct"
                                           | otherwise = 
    SStruct $ map (\(Field n t) e -> (n, storeFromExpr t e)) $ zip fs as
storeFromExpr' t e = error $ "storeFromExp " ++ show t ++ " " ++ show e

valFromIdent :: (?spec::Spec) => String -> Val
valFromIdent i = case lookupEnumerator i of
                      Just _  -> EnumVal i
                      Nothing -> error $ "valFromIdent: unknown enumerator: " ++ show i
