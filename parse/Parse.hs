{-# LANGUAGE TupleSections, FlexibleContexts #-}

module Parse where

import qualified Data.Map as M
import Control.Monad
import Data.Maybe

import Control.Applicative hiding (many,optional)
import Text.Parsec hiding ((<|>))
import Text.Parsec.String
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language
import Numeric
import Data.List
import Data.Bits
import Debug.Trace

reservedOpNames = ["!", "?", "~", "&", "|", "^", "=>", "||", "&&", "=", "==", "!=", "<", "<=", ">", ">=", "%", "+", "-", "*", "...", "::", "->"]
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
                 "import",
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
charLit    = T.charLiteral lexer

----------------------------------------------------------------
-- Common declarations that occur in different syntactic scopes
----------------------------------------------------------------
nopos = SourcePos "" 0 0

withPos x = (\s x e -> atPos x (s,e)) <$> getPosition <*> x <*> getPosition

quote :: String -> String
quote s = "\"" ++ s ++ "\""

ident = withPos $ identifier <|> (quote <$> stringLit)

staticsym = StaticSym <$> sepBy1 ident (reservedOp "::")
methname = withPos $ MethodRef nopos <$> sepBy1 ident dot

varDecl = withPos $ Var nopos <$> typeSpec 
                                  <*> ident 
                                  <*> optionMaybe (reservedOp "=" *> pexp)

typeDef = withPos $ TypeDecl nopos <$ reserved "typedef" <*> typeSpec <*> ident

slice = brackets $ (,) <$> expr <*> (colon *> expr)
index = brackets expr
field = dot *> ident
ptrfield = reservedOp "->" *> ident

-- Constant declaration
constant = withPos $ Const nopos <$  reserved "const" 
                                     <*> typeSpec 
                                     <*> ident 
                                     <*> (reservedOp "=" *> expr)

data TypeMod = ModPtr | ModDim PExpr

typeSpec = mkType <$> (withPos $ voidType <|> sintType <|> uintType <|> boolType <|> userType <|> enumType <|> structType) 
                  <*> (many $ (,) <$> ((ModDim <$> brackets expr) <|> (ModPtr <$ reservedOp "*")) <*> getPosition)

mkType :: TypeSpec -> [(TypeMod, Pos)] -> TypeSpec
mkType t [] = t
mkType t ((ModDim e, p):es) = mkType (ArrayType (fst $ pos t, snd p) t e)) es
mkType t ((ModPtr, p):es)   = mkType (PtrType (fst $ pos t, snd p) t) es

voidType   = VoidSpec     nopos <$  reserved "void"
sintType   = SIntSpec     nopos <$> (fromIntegral <$> angles decimal)
uintType   = UIntSpec     nopos <$> (fromIntegral <$> angles decimal)
boolType   = BoolSpec     nopos <$  reserved "bool"
userType   = UserTypeSpec nopos <$> staticsym
enumType   = EnumSpec     nopos <$  reserved "enum" <*> (braces $ commaSep1 enum)
structType = StructSpec   nopos <$  reserved "struct" <*> (braces $ many1 $ (,) <$> typeSpec <*> (ident <* semi))

enum = withPos $ Enumerator _ <$> ident <*> optionMaybe (reservedOp "=" *> expr)

-------------------------------------------------------------------------
-- Top-level scope
-------------------------------------------------------------------------

-- A TSL spec is a list of type, constant, and template declarations
data SpecItem = SpImport   Import
              | SpType     TypeDecl
              | SpConst    Const
              | SpTemplate Template

data Import = Import Pos Ident
instance PP Import where
    pp (Import _ file) = text "import" <+> char '<' <+> pp file <+> char '>'

-- A TSL spec is a list of template, type, and constant declarations.  
grammar = (optional whiteSpace) *> (many decl) <* eof
decl =  importDecl
    <|> (constDecl <* semi)
    <|> (typeDecl <* semi)
    <|> templateDecl
    <?> "constant, type or template declaration"

importDecl = SpImport <$> imp
imp = withPos $ Import nopos <$ reserved "import" <*> (reservedOp "<" *> (withPos $ manyTill anyChar (reservedOp ">")))

------------------------------------------------------------------------
-- Template scope
------------------------------------------------------------------------
templateDecl = SpTemplate <$> template

template = withPos $ mkTemplate  <$  reserved "template" 
                                <*> ident 
                                <*> option [] (parens $ commaSep $ templateImport) 
                                <*> ((many $ templateItem <* reservedOp ";") <*  reserved "endtemplate")

data TemplateItem = TDerive        Derive
                  | TTypeDecl      TypeDecl
                  | TConstDecl     Const
                  | TVarDecl       Var
                  | TInitBlock     Init
                  | TProcessDecl   Process
                  | TMethod        Method
                  | TGoalDecl      Goal
                  | TAssign        ContAssign

mkTemplate :: Ident -> [Port] -> [TemplateItem] -> Template
mkTemplate n ps is = Template nopos n ps drvs consts types vars inits procs meths
    where drvs = mapMaybe (\i -> case i of 
                                      TDerive d -> Just d
                                      _ -> Nothing) is
          consts = mapMaybe (\i -> case i of 
                                      TConstDecl c -> Just c
                                      _ -> Nothing) is
          types = mapMaybe (\i -> case i of 
                                      TTypeDecl t -> Just t
                                      _ -> Nothing) is
          vars = mapMaybe (\i -> case i of 
                                      TVarDecl v -> Just v
                                      _ -> Nothing) is
--          insts = mapMaybe (\i -> case i of 
--                                      TInstDecl inst -> Just inst
--                                      _ -> Nothing) is
          inits = mapMaybe (\i -> case i of 
                                      TInitBlock init -> Just init
                                      _ -> Nothing) is
          procs = mapMaybe (\i -> case i of 
                                      TProcessDecl p -> Just p
                                      _ -> Nothing) is
          meths = mapMaybe (\i -> case i of 
                                      TMethod m -> Just m
                                      _ -> Nothing) is


templateImport = withPos $ Port nopos <$> ident <*> ident

templateItem =  TDerive      <$> tderive
            <|> TTypeDecl    <$> typeDef
            <|> TConstDecl   <$> tconstDecl
            <|> TVarDecl     <$> try tvarDecl
            <|> TInitBlock   <$> tinitBlock
            <|> TProcessDecl <$> tprocessDecl
            <|> TTaskDecl    <$> ttaskDecl
            <|> TMethod      <$> tmethodDecl
            <|> TGoalDecl    <$> tgoalDecl
            <|> TAssign      <$> tassign
            <?> "declaration"

tderive      = withPos $ Derive nopos <$  reserved "derive" 
                                          <*> ident 
                                          <*> option [] (parens $ commaSep ident)
tconstDecl   = constant
tvarDecl     = withPos $ GVar nopos <$> (option False (True <$ reserved "export")) 
                                        <*> (option True (False <$ reserved "invisible")) 
                                        <*> varDecl
tinitBlock   = withPos $ Init nopos <$ reserved "init" <*> expr
tprocessDecl = withPos $ Process nopos <$  reserved "process" 
                                           <*> ident 
                                           <*> statement
tmethodDecl  = withPos $ Method nopos <$> (option False (True <$ reserved "export")) 
                                          <*> methCat
                                          <*> typeSpec
                                          <*> ident
                                          <*> (parens $ commaSep arg)
                                          <*> option (Left (Nothing, Nothing)) $
                                                  Left <$ reserved "before" <*> ((,) <$> (Just <$> statement) <*> optionMaybe (reserved "after" *> statement))
                                              <|> Left <$ reserved "after" <*> ((Nothing,) <$> (Just <$> statement))
                                              <|> Right <$> statement
tgoalDecl    = withPos $ Goal nopos <$  reserved "goal" 
                                        <*> (ident <* reservedOp "=") 
                                        <*> expr
tassign      = withPos $ ContAssign nopos <$  reserved "assign" 
                                              <*> (expr <* reservedOp "=") 
                                              <*> expr

methCat = Function <$> reserved "function"
          Procedure <$> reserved "procedure"
          Task <$ reserved "task" <*> option Invisible (  Controllable <$ reserved "controllable" 
                                                      <|> Uncontrollable <$ reserved "uncontrollable" 
                                                      <|> Invisible <$ reserved "invisible")

   
arg = withPos $ Arg nopos <$> (option ArgIn (ArgOut <$ reserved "out")) 
                              <*> typeSpec 
                              <*> ident



----------------------------------------------------------------
-- Statement
----------------------------------------------------------------
statement =  withPos <$>
           ( try svarDecl
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
         <?> "statement")

svarDecl = SVarDecl nopos <$> varDecl
sreturn  = SReturn nopos <$ reserved "return" <*> expr
sseq     = SSeq nopos <$> (braces $ many $ statement <* semi)
spar     = SPar nopos <$ reserved "fork" <*> (braces $ many $ statement <* semi)
sforever = SForever nopos <$ reserved "forever" <*> statement
sdo      = SDo nopos <$ reserved "do" <*> statement <* reserved "while" <*> (parens expr)
swhile   = SWhile nopos <$ reserved "while" <*> (parens expr) <*> statement
sfor     = SFor nopos <$ reserved "for" <*> (parens $ (,,) <$> (optionMaybe statement <* semi) <*> (expr <* semi) <*> statement) <*> statement
schoice  = SChoice nopos <$ reserved "choice" <*> (braces $ many $ statement <* semi)
spause   = SPause nopos <$ reserved "pause"
sstop    = SStop nopos <$ reserved "stop"
sinvoke  = SInvoke nopos <$ isinvoke <*> methname <*> (parens $ commaSep expr)
    where isinvoke = try $ lookAhead $ methname *> symbol "("
sassert  = SAssert nopos <$ reserved "assert" <*> (parens expr)
sassume  = SAssume nopos <$ reserved "assume" <*> (parens expr)
sassign  = SAssign nopos <$ isassign <*> expr <* reservedOp "=" <*> expr
    where isassign = try $ lookAhead $ expr *> symbol "="
site     = SITE nopos <$ reserved "if" <*> (parens expr) <*> statement <*> optionMaybe (reserved "else" *> statement)
scase    = (fmap uncurry (SCase nopos <$ reserved "case" <*> (parens expr))) <*> (braces $ (,) <$> (many $ (,) <$> expr <* colon <*> statement <* semi) 
                                                                                 <*> optionMaybe (reserved "default" *> colon *> statement <* semi))
smagic   = SMagic nopos <$ ismagic
                        <*> ((braces $ reservedOp "...") 
                         *> ((Left <$ reserved "using" <*> ident) <|> (Right <$ reserved "post" <*> expr)))
    where ismagic = try $ lookAhead $ symbol "{" *> reservedOp "..."

------------------------------------------------------------------
-- Expression
------------------------------------------------------------------

term = parens expr <|> term'

term' = withPos <$>
       ( estruct
     <|> eapply
--     <|> try etern
     <|> elit
     <|> ebool
     <|> eterm
     <|> ecase
     <|> econd)

estruct = EStruct nopos <$ isstruct <*> ident <*> (braces $ option (Left []) ((Left <$> namedfields) <|> (Right <$> anonfields)))
    where isstruct = try $ lookAhead $ ident *> symbol "{"
          anonfields = commaSep1 $ pexpr
          namedfields = commaSep1 $ ((,) <$ reservedOp "." <*> ident <* reservedOp "=" <*> expr)
eapply  = EApply nopos <$ isapply <*> methname <*> (parens $ commaSep expr)
    where isapply = try $ lookAhead $ methname *> symbol "("
eterm   = ETerm nopos <$> staticsym
ebool   = EBool nopos <$> ((True <$ reserved "true") <|> (False <$ reserved "false"))
elit    = lexeme elit'
etern   = ETernOp nopos <$> expr <* reservedOp "?" <*> expr <* colon <*> expr
ecase   = (fmap uncurry (ECase nopos <$ reserved "case" <*> (parens expr))) <*> (braces $ (,) <$> (many $ (,) <$> expr <* colon <*> expr <* semi) 
                                                                                              <*> optionMaybe (reserved "default" *> colon *> expr <* semi))
econd   = (fmap uncurry (ECond nopos <$ reserved "cond")) <*> (braces $ (,) <$> (many $ (,) <$> expr <* colon <*> expr <* semi) 
                                                                            <*> optionMaybe (reserved "default" *> colon *> expr <* semi))

elit' = (lookAhead $ char '\'' <|> digit) *> (fmap uncurry $ ELit nopos <$> width) <*> radval
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

expr =  (withPos $ ENonDet nopos <$ reservedOp "*")
    <|> buildExpressionParser table term
    <?> "expression"

table = [[postSlice, postIndex, postField, postPField]
        ,[prefix "!" Not, prefix "~" BNeg, prefix "-" UMinus, prefix "*" Deref, prefix "&" AddrOf]
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
        ,[binary "=>" Imp AssocRight]
        ,[binary "*" Mod AssocLeft]
        ,[binary "%" Mod AssocLeft]
        ,[binary "+" Plus AssocLeft]
        ,[binary "-" BinMinus AssocLeft]
        ]

postSlice  = Postfix $ try $ (\s end e -> ESlice (fst $ pos e, end) e s) <$> slice <*> getPosition
postIndex  = Postfix $ (\i end e -> EIndex (fst $ pos e, end) e i) <$> index <*> getPosition
postField  = Postfix $ (\f end e -> EField (fst $ pos e, end) e f) <$> field <*> getPosition
postPField = Postfix $ (\f end e -> EPField (fst $ pos e, end) e f) <$> ptrfield <*> getPosition

prefix name fun = Prefix $ (\start e -> EUnOp (start, snd $ pos e) fun e) <$> getPosition <* reservedOp name
binary name fun = Infix $ (\le re -> EBinOp (fst $ pos le, snd $ pos re) fun le re) <$ reservedOp name
