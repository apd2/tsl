{-# LANGUAGE TupleSections, FlexibleContexts #-}

module Main where

import Control.Applicative hiding (many,optional)
import Text.Parsec hiding ((<|>))
import Text.Parsec.String
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language
import Numeric
import Data.List
import Data.Bits
import System.Environment
import qualified Text.PrettyPrint as P
import Debug.Trace

import Syntax

reservedOpNames = ["!", "?", "~", "&", "|", "^", "->", "||", "&&", "=", "==", "!=", "<", "<=", ">", ">=", "%", "+", "-", "*", "..."]
reservedNames = ["after",
                 "assert",
                 "assign",
                 "assume", 
                 "before",
                 "bool",
                 "case",
                 "choice", 
                 "cond",
                 "const",
                 "controllable", 
                 "default",
                 "deriv",
                 "do", 
                 "else", 
                 "endtemplate",
                 "enum",
                 "export",
                 "false",
                 "forever", 
                 "fork", 
                 "function", 
                 "goal",
                 "if", 
                 "init",
                 "invisible", 
                 "out",
                 "pause",
                 "post", 
                 "procedure", 
                 "process",
                 "return",
                 "sint",
                 "stop", 
                 "struct",
                 "switch",
                 "task", 
                 "template", 
                 "true",
                 "typedef",
                 "uint",
                 "uncontrollable", 
                 "using", 
                 "void",
                 "while"]

lexer = T.makeTokenParser (emptyDef {T.commentStart      = "/*"
                                    ,T.commentEnd        = "*/"
                                    ,T.commentLine       = "//"
                                    ,T.nestedComments    = True
                                    ,T.identStart        = letter <|> char '_'
                                    ,T.identLetter       = alphaNum <|> char '_'
                                    ,T.reservedOpNames   = reservedOpNames
                                    ,T.reservedNames     = reservedNames
                                    ,T.caseSensitive     = True})

reservedOp = T.reservedOp lexer
reserved   = T.reserved lexer
identifier = T.identifier lexer
semiSep    = T.semiSep lexer
semiSep1   = T.semiSep1 lexer
colon      = T.colon lexer
commaSep   = T.commaSep lexer
commaSep1  = T.commaSep1 lexer
symbol     = T.symbol lexer
semi       = T.semi lexer
comma      = T.comma lexer
braces     = T.braces lexer
parens     = T.parens lexer
angles     = T.angles lexer
brackets   = T.brackets lexer
natural    = T.natural lexer
decimal    = T.decimal lexer
integer    = T.integer lexer
whiteSpace = T.whiteSpace lexer
lexeme     = T.lexeme lexer
dot        = T.dot lexer
stringLit  = T.stringLiteral lexer

----------------------------------------------------------------
-- Common declarations that occur in different syntactic scopes
----------------------------------------------------------------
withPos x = atPos <$> getPosition <*> x <*> getPosition

quote :: String -> String
quote s = "\"" ++ s ++ "\""

ident = identifier <|> 
        quote <$> stringLit
pident = withPos ident

fieldSelector = Field <$ dot <*> pident
indexSelector = Index <$> brackets pexpr
sym = Ident <$> pident <*> many (withPos $ fieldSelector <|> try indexSelector)
psym = withPos sym

varDecl = VarDecl <$> ptypeSpec <*> pident <*> optionMaybe (reservedOp "=" *> pexpr)

typeDef = TypeDef <$ reserved "typedef" <*> ptypeSpec <*> pident

slice = brackets $ (,) <$> pexpr <*> (colon *> pexpr)


-- Constant declaration
constDecl = ConstDecl <$> constant
constant = ConstDef <$ reserved "const" <*> ptypeSpec <*> pident <*> (reservedOp "=" *> pexpr)

-- Type declaration
typeDecl = TypeDecl <$> typeDef

ptypeSpec =  mkType <$> (withPos $ intType <|> boolType <|> userType <|> enumType <|> structType) 
                   <*> (many $ withPos $ brackets pexpr)

mkType :: PType -> [AtPos PExpr] -> PType
mkType t [] = t
mkType t@(AtPos _ (start,_)) ((AtPos e (_,end)):es) = mkType (AtPos (ArrayType t e) (start,end)) es

intType    = IntType <$> ((True <$ reserved "sint") <|> (False <$ reserved "uint")) <*> (fromIntegral <$> angles decimal)
boolType   = BoolType <$ reserved "bool"
userType   = UserType <$> pident
enumType   = EnumType <$ reserved "enum" <*> (braces $ commaSep1 $ (,) <$> ident <*> optionMaybe (reservedOp "=" *> pexpr))
structType = StructType <$ reserved "struct" <*> (braces $ many1 $ (,) <$> ptypeSpec <*> (pident <* semi))

-------------------------------------------------------------------------
-- Top-level scope
-------------------------------------------------------------------------

-- A TSL spec is a list of template, type, and constant declarations.  
grammar = (optional whiteSpace) *> (many pdecl) <* eof
decl =  (constDecl <* semi)
    <|> (typeDecl <* semi)
    <|> templateDecl
    <?> "constant, type or template declaration"

pdecl = withPos decl

------------------------------------------------------------------------
-- Template scope
------------------------------------------------------------------------
templateDecl = TemplateDecl <$> template

template = Template <$ reserved "template" <*> pident <*> option [] (parens $ commaSep $ templateImport) <*> ((many $ templateItem' <* reservedOp ";") <* reserved "endtemplate")
ptemplate = withPos template

templateImport = (,) <$> pident <*> pident

templateItem' = (,) <$> option False (True <$ reserved "export") <*> ptemplateItem
templateItem =  tderive
            <|> ttypeDecl
            <|> tconstDecl
            <|> tvarDecl
            <|> tinitBlock
            <|> tprocessDecl
            <|> ttaskDecl
            <|> tfuncDecl
            <|> tprocDecl
            <|> tgoalDecl
            <|> tassign
            <?> "declaration"

ptemplateItem = withPos templateItem

tderive      = TDerive <$ reserved "derive" <*> pident
ttypeDecl    = TTypeDecl <$> typeDef
tconstDecl   = TConstDecl <$> constant
tvarDecl     = TVarDecl <$> (option VarVis (VarInvis <$ reserved "invisible")) <*> varDecl
tinitBlock   = TInitBlock <$ reserved "init" <*> pstatement
tprocessDecl = TProcessDecl <$ reserved "process" <*> pident <*> pstatement
ttaskDecl    = TTaskDecl <$ reserved "task" <*> taskCat <*> signature <*> taskBody
tfuncDecl    = TFunctionDecl <$ reserved "function" <*> signature <*> optionMaybe pstatement
tprocDecl    = TProcedureDecl <$ reserved "procedure" <*> signature <*> optionMaybe pstatement
tgoalDecl    = TGoalDecl <$ reserved "goal" <*> (pident <* reservedOp "=") <*> pexpr
tassign      = TAssign <$ reserved "assign" <*> (plexpr <* reservedOp "=") <*> pexpr

taskBody = option (Left (Nothing, Nothing)) $
            Left <$ reserved "before" <*> ((,) <$> (Just <$> pstatement) <*> optionMaybe (reserved "after" *> pstatement))
        <|> Left <$ reserved "after" <*> ((Nothing,) <$> (Just <$> pstatement))
        <|> Right <$> pstatement

signature = Signature <$> (Nothing <$ reserved "void" <|> Just <$> ptypeSpec) <*> pident <*> (parens $ commaSep parg)
arg = Arg <$> (option ArgIn (ArgOut <$ reserved "out")) <*> ptypeSpec <*> pident
parg = withPos arg
taskCat = option Invis (Contr <$ reserved "controllable" <|> Uncontr <$ reserved "uncontrollable" <|> Invis <$ reserved "invisible")

----------------------------------------------------------------
-- Statement
----------------------------------------------------------------
statement =  try svarDecl
         <|> sreturn
         <|> smagic 
         <|> sseq
         <|> spar
         <|> sforever
         <|> sdo
         <|> swhile
         <|> sfor
         <|> schoice
         <|> spause
         <|> sstop
         <|> sassert
         <|> sassume
         <|> site
         <|> scase
         <|> sinvoke
         <|> sassign
         <?> "statement"

pstatement = withPos statement

svarDecl = SVarDecl <$> varDecl
sreturn  = SReturn <$ reserved "return" <*> pexpr
sseq     = SSeq <$> (braces $ many $ pstatement <* semi)
spar     = SPar <$ reserved "fork" <*> (braces $ many $ pstatement <* semi)
sforever = SForever <$ reserved "forever" <*> pstatement
sdo      = SDo <$ reserved "do" <*> pstatement <* reserved "while" <*> (parens pexpr)
swhile   = SWhile <$ reserved "while" <*> (parens pexpr) <*> pstatement
sfor     = SFor <$ reserved "for" <*> (parens $ (,,) <$> (optionMaybe pstatement <* semi) <*> (pexpr <* semi) <*> pstatement) <*> pstatement
schoice  = SChoice <$ reserved "choice" <*> (braces $ many $ pstatement <* semi)
spause   = SPause <$ reserved "pause"
sstop    = SStop <$ reserved "stop"
sinvoke  = SInvoke <$ isinvoke <*> psym <*> (parens $ commaSep pexpr)
    where isinvoke = try $ lookAhead $ psym *> symbol "("
sassert  = SAssert <$ reserved "assert" <*> (parens pexpr)
sassume  = SAssume <$ reserved "assume" <*> (parens pexpr)
sassign  = SAssign <$ isassign <*> plexpr <* reservedOp "=" <*> pexpr
    where isassign = try $ lookAhead $ plexpr *> symbol "="
site     = SITE <$ reserved "if" <*> (parens pexpr) <*> pstatement <*> optionMaybe (reserved "else" *> pstatement)
scase    = (fmap uncurry (SCase <$ reserved "case" <*> (parens pexpr))) <*> (braces $ (,) <$> (many $ (,) <$> pexpr <* colon <*> pstatement <* semi) 
                                                                                          <*> optionMaybe (reserved "default" *> colon *> pstatement <* semi))
smagic   = SMagic <$ ismagic
                  <*> ((braces $ reservedOp "...") 
                       *> ((Left <$ reserved "using" <*> pident) <|> (Right <$ reserved "post" <*> pexpr)))
    where ismagic = try $ lookAhead $ symbol "{" *> reservedOp "..."

------------------------------------------------------------------
-- Expression
------------------------------------------------------------------

pterm = parens pexpr <|> pterm'

term' =  estruct
     <|> eapply
--     <|> try etern
     <|> elit
     <|> ebool
     <|> eterm
     <|> ecase
     <|> econd 
pterm' = withPos term'

estruct = EStruct <$ isstruct <*> pident <*> (braces $ option (Left []) ((Left <$> namedfields) <|> (Right <$> anonfields)))
    where isstruct = try $ lookAhead $ pident *> symbol "{"
          anonfields = commaSep1 $ pexpr
          namedfields = commaSep1 $ ((,) <$ reservedOp "." <*> pident <* reservedOp "=" <*> pexpr)
eapply  = EApply <$ isapply <*> psym <*> (parens $ commaSep pexpr)
    where isapply = try $ lookAhead $ psym *> symbol "("
eterm   = ETerm <$> psym
ebool   = EBool <$> ((True <$ reserved "true") <|> (False <$ reserved "false"))
elit    = lexeme elit'
etern   = ETernOp <$> pexpr <* reservedOp "?" <*> pexpr <* colon <*> pexpr
ecase   = (fmap uncurry (ECase <$ reserved "case" <*> (parens pexpr))) <*> (braces $ (,) <$> (many $ (,) <$> pexpr <* colon <*> pexpr <* semi) 
                                                                                         <*> optionMaybe (reserved "default" *> colon *> pexpr <* semi))
econd   = (fmap uncurry (ECond <$ reserved "cond")) <*> (braces $ (,) <$> (many $ (,) <$> pexpr <* colon <*> pexpr <* semi) 
                                                                      <*> optionMaybe (reserved "default" *> colon *> pexpr <* semi))

elit' = (lookAhead $ char '\'' <|> digit) *> (fmap uncurry $ ELit <$> width) <*> radval
width = optionMaybe (try $ ((fmap fromIntegral parseDec) <* (lookAhead $ char '\'')))
radval =  ((,) <$> (Rad2  <$ (try $ string "'b")) <*> parseBin)
      <|> ((,) <$> (Rad8  <$ (try $ string "'o")) <*> parseOct)
      <|> ((,) <$> (Rad10 <$ (try $ string "'d")) <*> parseDec)
      <|> ((,) <$> (Rad16 <$ (try $ string "'h")) <*> parseHex)
      <|> ((Rad10,) <$> parseDec)
parseBin :: Stream s m Char => ParsecT s u m Integer
parseBin = readBin <$> (many1 $ (char '0') <|> (char '1'))
parseOct :: Stream s m Char => ParsecT s u m Integer
parseOct = (fst . head . readOct) <$> many1 octDigit
parseDec :: Stream s m Char => ParsecT s u m Integer
parseDec = (fst . head . readDec) <$> many1 digit
parseHex :: Stream s m Char => ParsecT s u m Integer
parseHex = (fst . head . readHex) <$> many1 hexDigit
readBin :: String -> Integer
readBin s = foldl' (\acc c -> (acc `shiftL` 1) +
                              case c of
                                   '0' -> 0
                                   '1' -> 1) 0 s

pexpr =  (withPos $ ENonDet <$ reservedOp "*")
     <|> buildExpressionParser table pterm
     <?> "expression"

table = [[postIndex]
        ,[prefix "!" Not, prefix "~" BNeg, prefix "-" UMinus]
        ,[binary "==" Eq AssocLeft, 
          binary "!=" Neq AssocLeft,
          binary "<"  Lt AssocNone, 
          binary "<=" Lte AssocNone, 
          binary ">"  Gt AssocNone, 
          binary ">=" Gte AssocNone]
        ,[binary "&" BAnd AssocLeft]
        ,[binary "^" BXor AssocLeft]
        ,[binary "|" BOr AssocLeft]
        ,[binary "&&" And AssocLeft]
        ,[binary "||" Or AssocLeft]
        ,[binary "->" Imp AssocRight]
        ,[binary "*" Mod AssocLeft]
        ,[binary "%" Mod AssocLeft]
        ,[binary "+" Plus AssocLeft]
        ,[binary "-" BinMinus AssocLeft]
        ]

postIndex = Postfix $ (\s end e@(AtPos _ (start,_)) -> AtPos (ESlice s e) (start,end)) <$> slice <*> getPosition

prefix name fun = Prefix $ (\start e@(AtPos _ (_,end)) -> AtPos (EUnOp fun e) (start,end)) 
                          <$> getPosition <* reservedOp name
binary name fun = Infix $ (\le@(AtPos _ (start,_)) re@(AtPos _ (_,end)) -> AtPos (EBinOp fun le re) (start,end)) 
                          <$ reservedOp name


lexpr = LExpr <$> psym <*> optionMaybe slice
plexpr = withPos lexpr


main = do
    args <- getArgs
    f <- case args of
             [] -> fail $ "File name required"
             _ -> return $ head args
    tsl <- readFile f
    --putStr tsl
    case parse grammar f tsl of
         Left e -> fail $ show e
         Right st -> do putStrLn "ok"
                        writeFile (f ++ ".out") $ P.render $ pp st
