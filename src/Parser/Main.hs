{-# OPTIONS_GHC -fno-warn-name-shadowing -fno-warn-type-defaults #-}
{-# LANGUAGE OverloadedStrings, CPP #-}
module Parser.Main where

import Control.Monad
import Data.Char (digitToInt, isUpper, isLower, isOctDigit, isHexDigit)
import Data.Either (partitionEithers)
import Data.List (partition)
import qualified Data.Map as Map
import Data.Maybe (isJust, fromMaybe)
import Text.Parsec
import Text.Parsec.Indentation

import Syntax.Surface hiding (decls, kind)
import qualified Syntax.Surface as AST
import Parser.Lexer
--import Parser.Monad

{- Section 3.2: Identifiers, symbols, and literals -}
-- FIXME: the names of the functions here don't quite match the names used
-- in the language report.

aConid  :: ParseM Id           -- basic form of constructor name
aConid   = try $ do
             i@(Ident s _ _) <- identifier isUpper
             guard (not (isBitLiteral s))   -- exclude anything that looks like a bit literal
             return i                       -- FIXME: this is ugly!
           where isBitLiteral ('B':rest) = not (null rest) && all isBinDigit rest
                 isBitLiteral ('O':rest) = not (null rest) && all (orUnderscore isOctDigit) rest
                 isBitLiteral ('X':rest) = not (null rest) && all (orUnderscore isHexDigit) rest
                 isBitLiteral _          = False
                 isBinDigit c            = c=='0' || c=='1' || c == '_'
                 orUnderscore f c        = c=='_' || f c

aConsym :: ParseM Id           -- basic form of constructor operator
aConsym  = operator (':'==)

conid   :: ParseM Id           -- constructor name in prefix position
conid    = (aConid  <|> try (parens aConsym)) <?> "constructor name"

consym  :: ParseM Id           -- constructor name in infix position
consym   = (aConsym <|> try (ticks aConid))   <?> "constructor symbol"


aVarid  :: ParseM Id           -- basic form of variable name
aVarid   = identifier isLower

aVarsym :: ParseM Id           -- basic form of variable operator
aVarsym  = operator (':'/=)

varid   :: ParseM Id           -- variable name in prefix position
varid    = (aVarid  <|> try (parens aVarsym)) <?> "variable name"

varsym  :: ParseM Id           -- variable name in infix position
varsym   = (aVarsym <|> try (ticks aVarid))   <?> "variable symbol"


intLiteral :: ParseM Integer
intLiteral = lexeme (choice [octalLiteral, hexLiteral, binaryLiteral, decimalLiteral]) <?> "integer literal"
    where decimalLiteral = do n <- decimal
                              ($ n) `fmap` siSuffix
          octalLiteral = do try (string "0o") <|> try (string "0O")
                            o <- octal
                            ($ o) `fmap` siSuffix
          hexLiteral = do try (string "0x") <|> try (string "0X")
                          h <- hexadecimal
                          ($ h) `fmap` siSuffix
          binaryLiteral = do try (string "0b") <|> try (string "0B")
                             b <- binary
                             ($ b) `fmap` siSuffix

          siSuffix :: ParseM (Integer -> Integer)
          siSuffix = (char 'K' >> return (*(2^10)))
                     <|> (char 'M' >> return (*(2^20)))
                     <|> (char 'G' >> return (*(2^30)))
                     <|> (char 'T' >> return (*(2^40)))
                     <|> return id

bitLiteral :: ParseM (Integer, Int)
bitLiteral = lexeme (choice [octalBitLiteral, hexBitLiteral, binaryBitLiteral]) <?> "bit-vector literal"
    where genericBitLiteral s base baseDigit v
              = do try (string s)
                   (n, digits) <- number_ base baseDigit
                   return (n, v * digits)
          octalBitLiteral  = genericBitLiteral "O" 8 octDigit 3
          hexBitLiteral    = genericBitLiteral "X" 16 hexDigit 4
          binaryBitLiteral = genericBitLiteral "B" 2 (oneOf "01") 1

literal :: ParseM Literal
literal = choice [ Numeric `fmap` intLiteral
                 , uncurry BitVector `fmap` bitLiteral ]

{- Section 3.3.1: Kinds -}

kind :: ParseM Kind
kind = chainr1 akind (do reservedOp "->"
                         return KFun)
    where akind = choice [ symbol   "*"    >> return KStar
                         , reserved "type" >> return KStar
                         , reserved "nat"  >> return KNat
                         , reserved "area" >> return KArea
                         , reserved "lab"  >> return KLabel
                         , varid           >>= return . KVar ]

{- Section 3.3.2: Types -}

arrowsym :: ParseM Id
arrowsym  = reservedOp "->" >> return "->"

tyconsym :: ParseM Id
tyconsym =    arrowsym
          <|> consym
          <|> varsym -- to support things like classes named *

tycon :: ParseM Id
tycon = conid
        <|> try (parens tyconsym)

atype :: ParseM Type
atype = do t <- located atype'
           ss <- many (dot >> located varid)
           return (dislocate (foldl tyselect t ss))
    where tyselect t id = at t (TySelect t id)

atype' = choice [ reservedOp "_" >> return TyWild
                , try (reserved "()") >> return (TyCon "Unit")
                , do char '#'
                     At l t <- located atype'
                     return (TyApp (At l (TyCon "Proxy")) (At l t))
                , (TyLabel . fromString) `fmap` stringLiteral
                , try (TyCon `fmap` tycon)
                , TyVar `fmap` varid
                , TyNat `fmap` intLiteral
                , try (parens (do n <- many1 (reservedOp ",")
                                  return (TyTupleCon (length n + 1))))
                , parens (do t <- located type_
                             choice [ do reservedOp ","
                                         ts <- commaSep1 (located type_)
                                         return (TyTuple (t:ts))
                                    , return (dislocate t) ]) ]

typeApp :: ParseM Type
typeApp = dislocate `fmap` chainl1 (located atype) (return app)
    where app t t' = at t (TyApp t t')

type_ :: ParseM Type
type_ = do t <- chain typeApp tyconsym TyInfix
           k <- optionMaybe (reservedOp "::" >> located kind)
           return $ case k of
                      Nothing -> dislocate t
                      Just k  -> TyKinded t k

{- Section 3.3.3 -}

predicate :: ParseM Pred
predicate = do p <- located type_
               eq <- optionMaybe (reservedOp "=" >> located type_)
               flag <- option Holds (reserved "fails" >> return Fails)
               return (Pred p eq flag)

qual :: ParseM t -> ParseM (Qual t)
qual p = do context <- option [] $ try $
                       do ps <- (parens (commaSep (located predicate)))
                                <|> (located predicate >>= return . singleton)
                          reservedOp "=>"
                          return ps
            (context :=>) `fmap` located p

{- 3.5: Patterns -}

pattern :: ParseM Pattern
pattern = dislocate `fmap` chain patApp (varsym <|> consym) PInfix <?> "pattern"

patApp = do ps <- many1 (located aPat)
            return (dislocate (foldl1 app ps))
    where app p p' = at p (PApp p p')
          aPat = do p <- located aPattern
                    option (dislocate p) $
                     do f <- reservedOp "." >> located varid
                        return (PApp (at p (PApp (at f (PVar "select")) p))
                                     (at f (PTyped (at f (PCon "Proxy"))
                                                   ([] :=> at f (TyApp (at f (TyCon "Proxy")) (TyLabel `fmap` f))))))

aPattern = choice [ do v <- try (varid `followedBy` reservedOp "@")
                       PAs v `fmap` located aPattern
                  , try (do ctor <- conid
                            args <- brackets (located fieldPattern `sepBy` symbol "|")
                            return (PLabeled ctor (map makePattern args)))
                  , reservedOp "_" >> return PWild
                  , try (reserved "()") >> return (PCon "Unit")
                  , try (PCon `fmap` conid)
                  , try (PLit `fmap` literal)
                  , try (PVar `fmap` varid)
                  , try (parens (do n <- many1 (reservedOp ",")
                                    return (PTupleCon (length n + 1))))
                  , try (parens aPattern')
                  , parens (PTuple `fmap` commaSep2 (located pattern)) ]
    where makePattern (At loc (f, Just p)) = At loc (FieldPattern f p)
          makePattern (At loc (f, Nothing)) = At loc (FieldPattern f (At loc (PVar f)))
          commaSep2 p = do v <- p
                           reservedOp ","
                           (v :) `fmap` commaSep1 p

aPattern' = choice [ do p <- try (located pattern `followedBy` reservedOp "::")
                        PTyped p `fmap` qual type_
                   , pattern ]

fieldPattern = varid +++ (optionMaybe (reservedOp "=" >> located pattern))

{- 3.4: Expressions and statements -}

expr     :: ParseM Expr
expr      = eInfix >>= optType

eInfix   :: ParseM (Located Expr)
eInfix    = chain eApp (varsym <|> consym) EInfix

eApp     :: ParseM Expr
eApp      = choice [ letExpr, ifExpr, caseExpr, applic ] <?> "expression"

stmt     :: ParseM Expr
stmt      = sInfix >>= optType

sInfix   :: ParseM (Located Expr)
sInfix    = chain sApp (varsym <|> consym) EInfix

sApp     :: ParseM Expr
sApp      = choice [ letStmt, ifStmt, caseStmt, applic ] <?> "statement"

optType  :: Located Expr -> ParseM Expr
optType e = do t <- optionMaybe (reservedOp "::" >> qual type_)
               return $ case t of
                          Nothing -> dislocate e
                          Just t  -> ETyped e t

{- 3.4.1: Applicative Expressions -}

applic :: ParseM Expr
applic = choice [ do reservedOp "\\"
                     patterns <- many1 (located aPattern)
                     reservedOp "->"
                     ELam patterns `fmap` located expr
                , do reserved "do"
                     requireBind =<< block
                , exprApp
                ]
    where requireBind e@(EBind {})       = return e
          requireBind (ELet ds (At l e)) = (ELet ds . At l) `fmap` requireBind e
          requireBind _                  = fail "Do block must contain at least one bind"

exprApp :: ParseM Expr
exprApp  = (do es <- many1 (located aExpr)
               return (dislocate (foldl1 app es))) <?> "application or atomic expression"
    where app e e' = at e (EApp e e')

aExpr :: ParseM Expr
aExpr = (do e <- located $ choice [ try (reserved "()") >> return (ECon "Unit")
                                  , do char '#'
                                       At l t <- located atype'
                                       return (ETyped (At l (ECon "Proxy")) ([] :=> At l (TyApp (At l (TyCon "Proxy")) (At l t))))
                                  , EVar `fmap` varid
                                  , try (do name <- located conid
                                            EStructInit name `fmap` brackets ((located varid +++ (reservedOp "<-" >> located expr)) `sepBy1` reservedOp "|"))
                                  , ECon `fmap` conid
                                  , ELit `fmap` try literal
                                  , try (parens (do e <- located aExpr
                                                    op <- located (varsym <|> consym)
                                                    return (ELeftSection e op)))
                                  , try (parens (do op <- located (varsym <|> consym)
                                                    e <- located aExpr
                                                    return (ERightSection op e)))
                                  , try (parens (do n <- many1 (reservedOp ",")
                                                    return (ETupleCon (length n + 1))))
                                  , parens (do e <- located expr
                                               choice [ do reservedOp ","
                                                           es <- commaSep (located expr)
                                                           return (ETuple (e:es))
                                                      , return (dislocate e) ]) ]
            fields <- many (try (symbol "." >> located varid) <||> try fieldValues)
            return (dislocate (foldl recordOperations e fields))) <?> "atomic expression"
    where fieldValues = brackets (singleField `sepBy` reservedOp "|")
          singleField = do name <- located varid
                           rhs  <- (reservedOp "=" >> located expr) <|> return (EVar `fmap` name)
                           return (name, rhs)
          recordOperations e (Left label) = at e (ESelect e label)
          recordOperations e (Right fields) = at e (EUpdate e fields)

{- 3.4.2: Blocks -}

data Line = LBind Id (Located Expr) | LLet Decls | LExpr (Located Expr)

block :: ParseM Expr
block = return . dislocate =<< build =<< layout (located line)
    where line = try (do name <- varid
                         reservedOp "<-"
                         LBind name `fmap` located stmt) <|>
                 LExpr `fmap` try (located stmt) <|>
                 (reserved "let" >> LLet `fmap` decls)

          build []                         = fail "empty do block"
          build [At _ (LExpr e)]           = return e
          build [_]                        = fail "blocks must end with expressions"
          build (At p (LBind id e) : rest) = (At p . EBind (Just id) e) `fmap` build rest
          build (At p (LLet ds) : rest)    = (At p . ELet ds) `fmap` build rest
          build (At p (LExpr e) : rest)    = (At p . EBind Nothing e) `fmap` build rest

{- 3.4.3: Local declarations -}

letExpr :: ParseM Expr
letExpr = do reserved "let"
             ds <- decls
             middle "in"
             ELet ds `fmap` located expr

letStmt :: ParseM Expr
letStmt = do reserved "let"
             ds <- decls
             middle "in"
             ELet ds `fmap` located block

{- 3.4.4: Conditionals -}

fromScrutinee    :: String -> ParseM Scrutinee
fromScrutinee kwd = try (do reserved kwd
                            optname <- optionMaybe varid
                            reservedOp "<-"
                            cond <- located stmt
                            return (ScFrom optname cond))

ifFrom :: ParseM Expr
ifFrom  = do scrutinee <- fromScrutinee "if"
             middle "then"
             cons <- located block
             alt <- optionMaybe (middle "else" >> located block)
             return (EIf scrutinee cons (fromMaybe returnNull alt))

ifExpr :: ParseM Expr
ifExpr  = ifFrom
          <|> do reserved "if"
                 cond <- located expr
                 middle "then"
                 cons <- located expr
                 middle "else"
                 alt <- located expr
                 return (EIf (ScExpr cond) cons alt)

ifStmt :: ParseM Expr
ifStmt  = ifFrom
          <|> do reserved "if"
                 cond <- located expr
                 middle "then"
                 cons <- located block
                 alt <- optionMaybe (middle "else" >> (try (located block) <|> located stmt))
                 return (EIf (ScExpr cond) cons (fromMaybe returnNull alt))

returnNull = introduced $ EApp (introduced $ EVar "return") (introduced $ ECon "Unit")

caseFrom :: ParseM Expr
caseFrom = do scrutinee <- fromScrutinee "case"
              middle "of"
              as <- alts block
              return (ECase scrutinee as)

caseExpr :: ParseM Expr
caseExpr  = caseFrom
            <|> do reserved "case"
                   cond <- located expr
                   middle "of"
                   as <- alts expr
                   return (ECase (ScExpr cond) as)

caseStmt :: ParseM Expr
caseStmt  = caseFrom
            <|> do reserved "case"
                   cond <- located expr
                   middle "of"
                   as <- alts block
                   return (ECase (ScExpr cond) as)

alts :: ParseM Expr -> ParseM [Alt]
alts e = layout (do p <- located pattern
                    r <- rhs (reservedOp "->") e
                    return (p :-> r))

rhs :: ParseM () -> ParseM Expr -> ParseM Rhs
rhs sep e = do g <- guards
               d <- optionMaybe (reserved "where" >> decls)
               return (g d)
    where guards = (Guarded `fmap` many1 (do reservedOp "|"
                                             g <- located expr
                                             sep
                                             body <- located e
                                             return (g, body)))
                   <|> (sep >> located e >>= return . Unguarded)

{- Declarations -}

equation :: ParseM Equation
equation = liftM2 (:=) (located pattern) (rhs (reservedOp "=") expr)

typeSignatures :: ParseM Id -> ParseM [Signature]
typeSignatures idParser = do ids <- try (commaSep1 idParser `followedBy` reservedOp "::")
                             t <- qual type_
                             return [Signature id t | id <- ids]

assoc :: ParseM Assoc
assoc = choice [ reserved "infixl" >> return LeftAssoc
               , reserved "infixr" >> return RightAssoc
               , reserved "infix" >> return NoAssoc ]

fixity :: ParseM [(Id, Bool, Located Fixity)]
fixity = do a <- assoc
            isType <- option False (reserved "type" >> return True)
            prec <- integer
            guard (0 <= prec && prec <= 9) <?> "precedence between 0 and 9"
            ids <- commaSep1 (located (varsym <|> consym <|> varid <|> conid <|> arrowsym))
            return [(id, isType, at idloc (Fixity a (fromIntegral prec))) | idloc@(At _ id) <- ids]

decl :: ParseM (Decls -> Decls)
decl = choice [ do sigs <- typeSignatures varid
                   return (\decls -> decls { signatures = signatures decls ++ sigs })
              , do eqn <- equation
                   return (\decls -> decls { equations = equations decls ++ [eqn] })
              , do ps <- fixity
                   return (\decls -> decls { fixities = Fixities (addFixities (valFixities (fixities decls)) not ps)
                                                                 (addFixities (typeFixities (fixities decls)) id ps) }) ]
    where addFixities m pred ps = foldl (\m f -> f m) m [ Map.insert id fix | (id, isType, fix) <- ps, pred isType ]

decls :: ParseM Decls
decls = do fcns <- layout decl
           return (foldl (\d f -> f d) emptyDecls fcns)

{- Top-level declarations -}

classDecl :: ParseM Class
classDecl = do reserved "class"
               lhs <- located type_
               determined <- optionMaybe (reservedOp "=" >> located type_)
               constraints <- option [] $ do reservedOp "|"
                                             constraints
               ds <- optionMaybe $ do reserved "where"
                                      decls
               return (Class lhs determined constraints ds)
    where constraints = commaSep1 (located ((Fundep `fmap` try fundep) <|> (Superclass `fmap` try predicate) <|> Opaque `fmap` opacity))
          fundep      = do xs <- many varid
                           reservedOp "->"
                           ys <- many1 varid
                           return (xs :~> ys)
          opacity     = do reserved "opaque"
                           varid

instanceDecl :: ParseM Instance
instanceDecl = reserved "instance" >> (Instance `fmap` (instanceClause `sepBy1` middle "else"))
    where instanceClause = do conclusion <- located predicate
                              preconditions <- option [] $ do reserved "if"
                                                              commaSep1 (located predicate)
                              methods <- optionMaybe $ reserved "where" >> decls
                              return (preconditions :=> conclusion,  methods)

requirementDecl :: ParseM Requirement
requirementDecl = do reserved "require"
                     ps <- commaSep1 (located predicate)
                     reserved "if"
                     Require ps `fmap` commaSep1 (located predicate)


synonymDecl :: ParseM Synonym
synonymDecl = do opaque <- option False (reserved "opaque" >> return True)
                 reserved "type"
                 lhs <- located type_
                 reservedOp "="
                 rhs <- qual type_
                 interface <- if opaque
                              then Just `fmap` option emptyDecls (reserved "where" >> decls)
                              else return Nothing
                 return (Synonym lhs rhs interface)

dataDecl :: ParseM Datatype
dataDecl = do opaque <- option False (reserved "opaque" >> return True)
              reserved "data"
              lhs <- located type_
              ctors <- option [] $ do reservedOp "="
                                      ctor `sepBy` reservedOp "|"
              drvlist <- deriveList
              interface <- if opaque
                           then Just `fmap` option emptyDecls (reserved "where" >> decls)
                           else return Nothing
              return (Datatype lhs ctors drvlist interface)
    where ctor = choice [ try $ do lhs <- located atype
                                   name <- located consym
                                   rhs <- located atype
                                   preds <- option [] $ reserved "if" >> commaSep1 (located predicate)
                                   return (Ctor name [] preds [at lhs (DataField Nothing lhs), at rhs (DataField Nothing rhs)])
                        , try $ do name <- located conid
                                   fields <- brackets (field `sepBy` reservedOp "|")
                                   preds <- option [] $ reserved "if" >> commaSep1 (located predicate)
                                   return (Ctor name [] preds (concat fields))
                        , do name <- located conid
                             ftypes <- many (located atype)
                             preds <- option [] $ reserved "if" >> commaSep1 (located predicate)
                             return (Ctor name [] preds [at t (DataField Nothing t) | t <- ftypes]) ]
          field = try (do labels <- commaSep1 (located varid)
                          reservedOp "::"
                          t <- located atype
                          return [At loc (DataField (Just lab) t) | At loc lab <- labels])

deriveList :: ParseM [Id]
deriveList  = option []
            $ do reserved "deriving"
                 parens (commaSep1 conid) <|> commaSep1 conid

bitdataDecl :: ParseM Bitdatatype
bitdataDecl = do reserved "bitdata"
                 id <- conid
                 width <- optionMaybe (reservedOp "/" >> (qual type_))
                 ctors <- option [] $ do reservedOp "="
                                         ctor `sepBy` reservedOp "|"
                 Bitdatatype id width ctors `fmap` deriveList
    where  ctor = do name <- located conid
                     fields <- concat `fmap` brackets (field `sepBy` reservedOp "|")
                     preds <- option [] $ reserved "if" >> commaSep1 (located predicate)
                     return (Ctor name [] preds fields)
           field = try (do labels <- commaSep1 (located label)
                           reservedOp "::"
                           typ <- located type_
                           return [at labelloc (LabeledField name typ def) | labelloc@(At _ (name, def)) <- labels]) <|>
                   (do e <- located literal
                       return [at e (ConstantField e)])
           label = do v   <- varid
                      def <- optionMaybe (reservedOp "=" >> located aExpr)
                      return (v, def)

structDecl :: ParseM Struct
structDecl = do reserved "struct"
                lid@(At _ id) <- located conid
                width <- optionMaybe (reservedOp "/" >> qual type_)
                fields <- brackets (field `sepBy` reservedOp "|")
                ps <- option [] $ reserved "if" >> commaSep1 (located predicate)
                Struct id width (Ctor lid [] ps (concat fields)) `fmap` deriveList

    where field = (do idInits <- commaSep1 (located varid +++ optionMaybe (reservedOp "<-" >> located exprApp))
                      reservedOp "::"
                      t <- located type_
                      return [At l (StructRegion (Just (StructField id init)) t) | (id@(At l _), init) <- idInits]) <|>
                  (do t@(At l _) <- located (type_)
                      return [At l (StructRegion Nothing t)])

areaDecl :: ParseM Area
areaDecl = do v <- option False (reserved "volatile" >> return True)
              reserved "area"
              ids <- commaSep $ do id <- located varid
                                   minit <- optionMaybe $ reservedOp "<-" >> eInfix
                                   return (id, minit)
              reservedOp "::"
              t <- qual type_
              mdecls <- optionMaybe $ reserved "where" >> decls
              return (Area v ids t mdecls)

primitive :: ParseM [Primitive]
primitive = do reserved "primitive"
               choice [ do reserved "type"
                           names <- commaSep (located tycon)
                           reservedOp "::"
                           k <- located kind
                           return [PrimType (At l (TyKinded (fmap TyCon name) k)) | name@(At l _) <- names]
                      , do public <- option True (reserved "private" >> return False)
                           ss <- typeSignatures (varid <|> conid)
                           let (ctors, values) = partition (\(Signature name _) -> isConId name) ss
                           return ([PrimValue s (fromId id) public | s@(Signature id _) <- values] ++
                                   [PrimCon s (fromId id) public | s@(Signature id _) <- ctors])
                      , do Class t determined constraints decls <- classDecl
                           constraints' <- mapM filterConstraint constraints
                           return [PrimClass t determined constraints' decls] ]
    where filterConstraint (At location (Superclass {})) = fail "Illegal superclass constraint on primitive class declaration"
          filterConstraint (At location (Fundep fd))     = return (At location fd)

topDecl :: ParseM (Program -> Program)
topDecl = choice [ do fcn <- decl
                      return (\p -> p { AST.decls = fcn (AST.decls p) })
                 , do cls <- located classDecl
                      return (\p -> p { classes = classes p ++ [cls] })
                 , do ins <- located instanceDecl
                      return (\p -> p { instances = instances p ++ [ins] })
                 , do rq <- located requirementDecl
                      return (\p -> p { requirements = requirements p ++ [rq] })
                 , do syn <- try (located synonymDecl)
                      return (\p -> p { synonyms = synonyms p ++ [syn] })
                 , do dat <- located dataDecl
                      return (\p -> p { datatypes = datatypes p ++ [dat] })
                 , do bit <- located bitdataDecl
                      return (\p -> p { bitdatatypes = bitdatatypes p ++ [bit] })
                 , do str <- located structDecl
                      return (\p -> p { structures = structures p ++ [str] })
                 , do are <- located areaDecl
                      return (\p -> p { areas = areas p ++ [are] })
                 , do At l prims <- located primitive
                      return (\p -> p { primitives = primitives p ++ map (At l) prims })
                 , do reserved "requires"
                      lnames <- commaSep1 (located (map fromId `fmap` dotSep1 (varid <|> conid)))
                      return (\p -> p { requires = requires p ++ lnames }) ]

program :: ParseM Program
program = do whiteSpace
             topDecls <- layout topDecl
             return (foldl (\p f -> f p) emptyProgram topDecls)

{- Utilities -}

terminal :: ParseM a -> ParseM a
terminal p = do
  x <- p
  eof
  return x

singleton :: a -> [a]
singleton = (:[])

followedBy :: ParseM a -> ParseM b -> ParseM a
followedBy a b = do x <- a; b; return x

p +++ q = do x <- p; y <- q; return (x,y)
p <||> q = Left `fmap` p <|> Right `fmap` q

chain :: ParseM t -> ParseM u -> (Located t -> [(Located u, Located t)] -> t) -> ParseM (Located t)
chain operand operator ctor =
    do (first, rest) <- chainl1 (one (located operand))
                                (do op <- located operator
                                    return (\left right -> combine left op right))
       return (if null rest then first else at first (ctor first rest))
    where one p = p +++ return []
          combine (first, rest) op (new, []) = (first, rest ++ [(op, new)])

located p = do start <- getPosition
               v <- p
               end <- getPosition
               return (At (Location start end) v)

unlocated p = do At _ x <- p
                 return x

{- Here be dragons -}
