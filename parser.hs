{-# LANGUAGE TupleSections #-}

module Main where

import Control.Applicative hiding (many)

import Text.Parsec hiding ((<|>))
import Text.Parsec.String
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language

import Syntax

reservedOpNames = ["!", "~", "&", "|", "^", "->", "||", "&&", "=", "==", "!=", "<", "<=", ">", ">=", "%", "+", "-", "*", "..."]
reservedNames = ["assert",
                 "assign",
                 "assume", 
                 "bool",
                 "case",
                 "choice", 
                 "controllable", 
                 "default",
                 "do", 
                 "else", 
                 "endtemplate",
                 "export",
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
                 "sint",
                 "stop", 
                 "switch",
                 "task", 
                 "template", 
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
withPos x = AtPos <$> x <*> getPosition

quote :: String -> String
quote s = "\"" ++ s ++ "\""

ident = identifier <|> 
        quote <$> stringLit
pident = withPos ident

fieldSelector = Field <$ dot <*> pident
indexSelector = Index <$> brackets pexpr
sym = Ident <$> pident <*> many (withPos $ fieldSelector <|> (try indexSelector))
psym = withPos sym

varDecl = VarDecl <$> ptypeSpec <*> pident

typeDef = TypeDef <$ reserved "typedef" <*> ptypeSpec <*> pident

slice = brackets $ f <$> natural <*> (colon *> natural)
    where f l r = (fromIntegral r, fromIntegral l)


-- Constant declaration
constDecl = ConstDecl <$> constant
constant = ConstDef <$ reserved "const" <*> ptypeSpec <*> pident <*> ((reservedOp "=" *> pexpr) <* semi)

-- Type declaration
typeDecl = TypeDecl <$> typeDef

typeSpec =  try arrayType 
        <|> intType 
        <|> boolType 
        <|> userType 
        <|> enumType 
        <|> structType 

intType    = IntType <$> ((True <$ reserved "sint") <|> (False <$ reserved "uint")) <*> (fromIntegral <$> angles decimal)
boolType   = BoolType <$ reserved "bool"
userType   = UserType <$> pident
enumType   = EnumType <$ reserved "enum" <*> (braces $ commaSep1 $ (,) <$> ident <*> optionMaybe (reservedOp "=" *> pexpr))
structType = StructType <$ reserved "struct" <*> (braces $ many1 $ (,) <$> ptypeSpec <*> (pident <* semi))
arrayType  = ArrayType <$> ptypeSpec <*> brackets pexpr

ptypeSpec = withPos typeSpec

-------------------------------------------------------------------------
-- Top-level scope
-------------------------------------------------------------------------

-- A TSL spec is a list of template, type, and constant declarations.  
tslSpec = many (pdecl <* reservedOp ";")
decl =  constDecl 
    <|> (typeDecl <* semi)
    <|> templateDecl

pdecl = withPos decl

------------------------------------------------------------------------
-- Template scope
------------------------------------------------------------------------
templateDecl = TemplateDecl <$ reserved "template" <*> pident <*> ptemplate

template = Template <$> option [] (parens $ commaSep $ templateImport) <*> ((many $ templateItem' <* reservedOp ";") <* reserved "endtemplate")
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

ptemplateItem = withPos templateItem

tderive      = TDerive <$ reserved "derive" <*> pident
ttypeDecl    = TTypeDecl <$> typeDef
tconstDecl   = TConstDecl <$> constant
tvarDecl     = TVarDecl <$> (option VarVis (VarInvis <$ reserved "invisible")) <*> varDecl
tinitBlock   = TInitBlock <$ reserved "init" <*> pstatement
tprocessDecl = TProcessDecl <$ reserved "process" <*> pident <*> pstatement
ttaskDecl    = TTaskDecl <$ reserved "task" <*> taskCat <*> signature <*> taskBody
tfuncDecl    = TFunctionDecl <$> signature <*> pstatement
tprocDecl    = TProcedureDecl <$> signature <*> pstatement
tgoalDecl    = TGoalDecl <$ reserved "goal" <*> (pident <* reservedOp "=") <*> pexpr
tassign      = TAssign <$ reserved "assign" <*> (plexpr <* reservedOp "=") <*> pexpr

taskBody =  Left <$ reserved "before" <*> ((,) <$> (Just <$> pstatement) <*> optionMaybe (reserved "after" *> pstatement))
        <|> Left <$ reserved "after" <*> ((Nothing,) <$> (Just <$> pstatement))
        <|> Right <$> pstatement
        <|> Left (Nothing,Nothing) <$ empty

signature = Signature <$> (Nothing <$ reserved "void" <|> Just <$> ptypeSpec) <*> pident <*> (parens $ commaSep parg)
arg = Arg <$> (option ArgIn (ArgOut <$ reserved "out")) <*> ptypeSpec <*> pident
parg = withPos arg
taskCat = option Invis (Contr <$ reserved "controllable" <|> Uncontr <$ reserved "uncontrollable" <|> Invis <$ reserved "invisible")

----------------------------------------------------------------
-- Statement
----------------------------------------------------------------
statement =  try svarDecl
         <|> try sseq
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
         <|> try smagic 
         <|> try sinvoke
         <|> try sassign

pstatement = withPos statement

svarDecl = SVarDecl <$> varDecl
sseq     = SSeq <$> (braces $ many $ pstatement <* semi)
spar     = SPar <$ reserved "fork" <*> (braces $ many $ pstatement <* semi)
sforever = SForever <$ reserved "forever" <*> pstatement
sdo      = SDo <$ reserved "do" <*> pstatement <* reserved "while" <*> (parens pexpr)
swhile   = SWhile <$ reserved "while" <*> (parens pexpr) <*> pstatement
sfor     = SFor <$ reserved "for" <*> (parens $ (,,) <$> (optionMaybe pstatement <* semi) <*> (pexpr <* semi) <*> pstatement) <*> pstatement
schoice  = SChoice <$ reserved "choice" <*> (braces $ many $ pstatement <* semi)
spause   = SPause <$ reserved "pause"
sstop    = SStop <$ reserved "stop"
sinvoke  = SInvoke <$> psym <*> (parens $ commaSep pexpr)
sassert  = SAssert <$ reserved "assert" <*> (parens pexpr)
sassume  = SAssume <$ reserved "assume" <*> (parens pexpr)
sassign  = SAssign <$> plexpr <* reservedOp "=" <*> pexpr
site     = SITE <$ reserved "if" <*> (parens pexpr) <*> pstatement <*> optionMaybe (reserved "else" *> pstatement)
scase    = (fmap uncurry (SCase <$ reserved "case" <*> (parens pexpr))) <*> (braces $ (,) <$> (many $ (,) <$> pexpr <* colon <*> pstatement <* semi) 
                                                                                          <*> optionMaybe (reserved "default" *> colon *> pstatement <* semi))
smagic   = SMagic <$ (braces $ reservedOp "...") 
                 <*> ((Left <$ reserved "using" <*> pident) <|> (Right <$ reserved "post" <*> (parens pexpr)))

------------------------------------------------------------------
-- Expression
------------------------------------------------------------------
expr = undefined 
pexpr = withPos expr

lexpr = LExpr <$> psym <*> optionMaybe slice
plexpr = withPos lexpr


main = putStrLn "TSL v2 parser"
