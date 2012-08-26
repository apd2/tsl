{-# LANGUAGE TupleSections, FlexibleContexts, ScopedTypeVariables #-}

module Parse where

import qualified Data.Map as M
import Control.Monad
import Data.Maybe
import qualified Text.PrettyPrint as P

import Control.Applicative hiding (many,optional,Const)
import Text.Parsec hiding ((<|>))
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Pos
import qualified Text.Parsec.Token as T
import Text.Parsec.Language
import Numeric
import Data.List
import Data.Bits
import Debug.Trace

import PP
import Pos
import Name
import Expr
import Statement
import Process
import Template
import Var
import TypeSpec
import Method
import Const

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
                 "break",
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
nopos::Pos = (initialPos "",initialPos "")

withPos x = (\s x e -> atPos x (s,e)) <$> getPosition <*> x <*> getPosition

quote :: String -> String
quote s = "\"" ++ s ++ "\""

ident = withPos $ Ident nopos <$> (identifier <|> (quote <$> stringLit))

staticsym = sepBy1 ident (reservedOp "::")
methname = withPos $ MethodRef nopos <$> sepBy1 ident dot

varDecl = withPos $ Var nopos <$> typeSpec 
                                  <*> ident 
                                  <*> optionMaybe (reservedOp "=" *> expr)

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

data TypeMod = ModPtr | ModDim Expr

typeSpec = mkType <$> (withPos $ sintType <|> uintType <|> boolType <|> userType <|> enumType <|> structType) 
                  <*> (many $ (,) <$> ((ModDim <$> brackets expr) <|> (ModPtr <$ reservedOp "*")) <*> getPosition)

mkType :: TypeSpec -> [(TypeMod, SourcePos)] -> TypeSpec
mkType t [] = t
mkType t ((ModDim e, p):es) = mkType (ArraySpec (fst $ pos t, p) t e) es
mkType t ((ModPtr, p):es)   = mkType (PtrSpec (fst $ pos t, p) t) es

sintType   = SIntSpec     nopos <$  reserved "sint" <*> (fromIntegral <$> angles decimal)
uintType   = UIntSpec     nopos <$  reserved "uint" <*> (fromIntegral <$> angles decimal)
boolType   = BoolSpec     nopos <$  reserved "bool"
userType   = UserTypeSpec nopos <$> staticsym
enumType   = EnumSpec     nopos <$  reserved "enum" <*> (braces $ commaSep1 enum)
structType = StructSpec   nopos <$  reserved "struct" <*> (braces $ many1 $ withPos $ Field nopos <$> typeSpec <*> (ident <* semi))

enum = withPos $ Enumerator nopos <$> ident

-------------------------------------------------------------------------
-- Top-level scope
-------------------------------------------------------------------------

-- A TSL spec is a list of type, constant, and template declarations
data SpecItem = SpImport   Import
              | SpType     TypeDecl
              | SpConst    Const
              | SpTemplate Template

instance PP SpecItem where
    pp (SpImport i)   = pp i
    pp (SpType t)     = pp t
    pp (SpConst c)    = pp c
    pp (SpTemplate t) = pp t

data Import = Import Pos Ident
instance PP Import where
    pp (Import _ file) = P.text "import" P.<+> P.char '<' P.<> pp file P.<> P.char '>'
instance WithPos Import where
    pos (Import p _)     = p
    atPos (Import _ i) p = Import p i

-- A TSL spec is a list of template, type, and constant declarations.  
grammar = (optional whiteSpace) *> (many decl) <* eof
decl =  (SpImport <$> imp)
    <|> (SpConst <$> constant <* semi)
    <|> (SpType <$> typeDef <* semi)
    <|> (SpTemplate <$> template)
    <?> "constant, type or template declaration"

imp = withPos $ Import nopos <$ reserved "import" <*> (reservedOp "<" *> (withPos $ Ident nopos <$> manyTill anyChar (reservedOp ">")))

------------------------------------------------------------------------
-- Template scope
------------------------------------------------------------------------

template = withPos $ mkTemplate  <$  reserved "template" 
                                <*> ident 
                                <*> option [] (parens $ commaSep $ templateImport) 
                                <*> ((many $ templateItem <* reservedOp ";") <*  reserved "endtemplate")

data TemplateItem = TDerive        Derive
                  | TTypeDecl      TypeDecl
                  | TInstDecl      Instance
                  | TConstDecl     Const
                  | TVarDecl       GVar
                  | TInitBlock     Init
                  | TProcessDecl   Process
                  | TMethod        Method
                  | TGoalDecl      Goal
                  | TAssign        ContAssign

mkTemplate :: Ident -> [Port] -> [TemplateItem] -> Template
mkTemplate n ps is = Template nopos n ps drvs consts types vars insts inits procs meths goals
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
          insts = mapMaybe (\i -> case i of 
                                      TInstDecl inst -> Just inst
                                      _ -> Nothing) is
          inits = mapMaybe (\i -> case i of 
                                      TInitBlock init -> Just init
                                      _ -> Nothing) is
          procs = mapMaybe (\i -> case i of 
                                      TProcessDecl p -> Just p
                                      _ -> Nothing) is
          meths = mapMaybe (\i -> case i of 
                                      TMethod m -> Just m
                                      _ -> Nothing) is
          goals =  mapMaybe (\i -> case i of 
                                      TGoalDecl g -> Just g
                                      _ -> Nothing) is



templateImport = withPos $ Port nopos <$> ident <*> ident

templateItem =  TDerive      <$> tderive
            <|> TInstDecl    <$> instDecl
            <|> TTypeDecl    <$> typeDef
            <|> TConstDecl   <$> constant
            <|> TVarDecl     <$> try tvarDecl
            <|> TInitBlock   <$> tinitBlock
            <|> TProcessDecl <$> tprocessDecl
            <|> TMethod      <$> tmethodDecl
            <|> TGoalDecl    <$> tgoalDecl
            <|> TAssign      <$> tassign
            <?> "declaration"

tderive      = withPos $ Derive nopos <$  reserved "derive" 
                                      <*> ident 
                                      <*> option [] (parens $ commaSep ident)
instDecl     = withPos $ Instance nopos <$  reserved "instance"
                                        <*> ident
                                        <*> ident
                                        <*> (parens $ commaSep ident)
tvarDecl     = withPos $ GVar nopos <$> (option False (True <$ reserved "export")) 
--                                        <*> (option True (False <$ reserved "invisible")) 
                                        <*> varDecl
tinitBlock   = withPos $ Init nopos <$ reserved "init" <*> expr
tprocessDecl = withPos $ Process nopos <$  reserved "process" 
                                       <*> ident 
                                       <*> statement
tmethodDecl  = withPos $ Method nopos <$> (option False (True <$ reserved "export")) 
                                          <*> methCateg
                                          <*> ((Nothing <$ reserved "void") <|> (Just <$> typeSpec))
                                          <*> ident
                                          <*> (parens $ commaSep arg)
                                          <*> (option (Left (Nothing, Nothing)) $
                                                   Left <$ reserved "before" <*> ((,) <$> (Just <$> statement) <*> optionMaybe (reserved "after" *> statement))
                                               <|> Left <$ reserved "after" <*> ((Nothing,) <$> (Just <$> statement))
                                               <|> Right <$> statement)
tgoalDecl    = withPos $ Goal nopos <$  reserved "goal" 
                                    <*> (ident <* reservedOp "=") 
                                    <*> expr
tassign      = withPos $ ContAssign nopos <$  reserved "assign" 
                                          <*> (expr <* reservedOp "=") 
                                          <*> expr 

methCateg =  (Function <$ reserved "function")
         <|> (Procedure <$ reserved "procedure")
         <|> (Task <$ reserved "task" <*> option Invisible (  Controllable <$ reserved "controllable" 
                                                          <|> Uncontrollable <$ reserved "uncontrollable" 
                                                          <|> Invisible <$ reserved "invisible"))
   
arg = withPos $ Arg nopos <$> (option ArgIn (ArgOut <$ reserved "out")) 
                              <*> typeSpec 
                              <*> ident



----------------------------------------------------------------
-- Statement
----------------------------------------------------------------
statement =  withPos $
           ( (try svarDecl)
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
         <|> sbreak
         <|> sassert
         <|> sassume
         <|> site
         <|> scase
         <|> sinvoke
         <|> sassign
         <?> "statement")

svarDecl = SVarDecl nopos <$> varDecl
sreturn  = SReturn nopos <$ reserved "return" <*> (optionMaybe expr)
sseq     = SSeq nopos <$> (braces $ many $ statement <* semi)
spar     = SPar nopos <$ reserved "fork" <*> (braces $ many $ statement <* semi)
sforever = SForever nopos <$ reserved "forever" <*> statement
sdo      = SDo nopos <$ reserved "do" <*> statement <* reserved "while" <*> (parens expr)
swhile   = SWhile nopos <$ reserved "while" <*> (parens expr) <*> statement
sfor     = SFor nopos <$ reserved "for" <*> (parens $ (,,) <$> (optionMaybe statement <* semi) <*> (expr <* semi) <*> statement) <*> statement
schoice  = SChoice nopos <$ reserved "choice" <*> (braces $ many $ statement <* semi)
spause   = SPause nopos <$ reserved "pause"
sstop    = SStop nopos <$ reserved "stop"
sbreak   = SBreak nopos <$ reserved "break"
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

term' = withPos $
       ( estruct
     <|> eapply
--     <|> try etern
     <|> elit
     <|> ebool
     <|> eterm
     <|> ecase
     <|> econd)

estruct = EStruct nopos <$ isstruct <*> staticsym <*> (braces $ option (Left []) ((Left <$> namedfields) <|> (Right <$> anonfields)))
    where isstruct = try $ lookAhead $ staticsym *> symbol "{"
          anonfields = commaSep1 expr
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

elit' = (lookAhead $ char '\'' <|> digit) *> (do w         <- width
                                                 ((s,r),v) <- sradval
                                                 mkLit w s r v)

width = optionMaybe (try $ ((fmap fromIntegral parseDec) <* (lookAhead $ char '\'')))
sradval =  ((,) <$> ((False, Rad2)  <$ (try $ string "'b"))  <*> parseBin)
       <|> ((,) <$> ((True,  Rad2)  <$ (try $ string "'sb")) <*> parseBin)
       <|> ((,) <$> ((False, Rad8)  <$ (try $ string "'o"))  <*> parseOct)
       <|> ((,) <$> ((True,  Rad8)  <$ (try $ string "'so")) <*> parseOct)
       <|> ((,) <$> ((False, Rad10) <$ (try $ string "'d"))  <*> parseDec)
       <|> ((,) <$> ((True,  Rad10) <$ (try $ string "'sd")) <*> parseSDec)
       <|> ((,) <$> ((False, Rad16) <$ (try $ string "'h"))  <*> parseHex)
       <|> ((,) <$> ((True,  Rad16) <$ (try $ string "'sh")) <*> parseHex)
       <|> (((False,Rad10),) <$> parseDec)
parseBin :: Stream s m Char => ParsecT s u m Integer
parseBin = readBin <$> (many1 $ (char '0') <|> (char '1'))
parseOct :: Stream s m Char => ParsecT s u m Integer
parseOct = (fst . head . readOct) <$> many1 octDigit
parseDec :: Stream s m Char => ParsecT s u m Integer
parseDec = (fst . head . readDec) <$> many1 digit
parseSDec = (\m v -> m * v)
            <$> (option 1 ((-1) <$ reservedOp "-"))
            <*> ((fst . head . readDec) <$> many1 digit)
parseHex :: Stream s m Char => ParsecT s u m Integer
parseHex = (fst . head . readHex) <$> many1 hexDigit
readBin :: String -> Integer
readBin s = foldl' (\acc c -> (acc `shiftL` 1) +
                              case c of
                                   '0' -> 0
                                   '1' -> 1) 0 s

mkLit :: Maybe Int -> Bool -> Radix -> Integer -> ParsecT s u m Expr
mkLit Nothing  False Rad10 v                       = return $ ELit nopos (msb v + 1) False Rad10 v
mkLit Nothing  False r     v                       = return $ ELit nopos (msb v + 1) False r     v
mkLit Nothing  True  r     v                       = fail "Explicit width required for signed literal"
mkLit (Just w) False r     v | w == 0              = fail "Unsigned literals must have width >0"
                             | msb v < w           = return $ ELit nopos w False r v
                             | otherwise           = fail "Value exceeds specified width"
mkLit (Just w) True  Rad10 v | w < 2               = fail "Signed literals must have width >1"
                             | (msb $ abs v) < w-1 = return $ ELit nopos w True Rad10 v
                             | otherwise           = fail "Value exceeds specified width"
mkLit (Just w) True  r     v | w < 2               = fail "Signed literals must have width >1"
                             | msb v == w - 1      = do let v' = (foldl' (\v i -> complementBit v i) v [0..w-1]) + 1
                                                        return $ ELit nopos w True r (-v')
                             | msb v < w - 1       = return $ ELit nopos w True r v
                             | otherwise           = fail "Value exceeds specified width"

-- Determine the most significant set bit of a non-negative number 
-- (returns 0 if not bits are set)
msb :: (Bits b) => b -> Int
msb 0 = 0
msb 1 = 0
msb n = 1 + (msb $ n `shiftR` 1)


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
