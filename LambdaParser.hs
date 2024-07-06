module LambdaParser where
import LambdaTypes
import Text.Parsec
    ( letter, chainl1, (<|>), runParser, try, Parsec )
import qualified Text.Parsec.Token as L
import Text.Parsec.Language (emptyDef)
import Data.Char ( isUpper )


lingDef = emptyDef
          { L.commentStart = "{-"
           ,L.commentEnd   = "-}"
           ,L.commentLine  = "--"
           ,L.identStart   = letter
           ,L.identLetter  = letter
           ,L.reservedNames = ["let", "in", "if", "then", "else", "case", "of", "True", "False"]
           ,L.reservedOpNames = ["=", "->"]
          }

lexical = L.makeTokenParser lingDef


symbol     = L.symbol lexical
parens     = L.parens lexical
identifier = L.identifier lexical
reserved   = L.reserved lexical
reservedOp = L.reservedOp lexical
integer    = L.integer lexical

--------- Parser -----------------
parseExpr = runParser expr [] "lambda-calculus"

expr :: Parsec String u Expr
expr = chainl1 parseNonApp $ return App

isConst (x:xs) = isUpper x
isVar (x:xs) = not (isUpper x)
parseVarOrConst = do i <- identifier
                     return (if isVar i then Var i else Const i)

lamAbs = do symbol "\\"
            i <- identifier
            symbol "."
            Lam i <$> expr

parseLitBool = do b <- do {reserved "True"; return True} <|> do {reserved "False"; return False}
                  return (LitBool b)

parseLitInt = do LitInt <$> integer

parseLitChar = do symbol "\'"
                  l <- letter
                  symbol "\'"
                  return (LitChar l)

parseLit = parseLitChar
           <|> parseLitBool
           <|> parseLitInt

parseLet = do reserved "let"
              i <- identifier
              reservedOp "="
              e <- expr
              reserved "in"
              Let (i, e) <$> expr

parseIf = do reserved "if"
             c <- expr
             reserved "then"
             e <- expr
             reserved "else"
             If c e <$> expr

parsePair = do symbol "("
               e <- expr
               symbol ","
               e' <- expr
               symbol ")"
               return (App (App (Const "(,)") e) e')

parsePats = try (do {p <- parsePat; ps <- parsePats; return (p:ps);})
            <|> (do {return [];})

parsePatVarOrCons = do c <- identifier
                       if isConst c then
                        do PCon c <$> parsePats
                       else return (PVar c)

parsePatPair = do symbol "("
                  p <- parsePat
                  symbol ","
                  p' <- parsePat
                  symbol ")"
                  return (PCon "(,)" [p, p'])

parsePatLit = do PLit <$> parseLit

parsePatExpr = do p <- parsePat
                  reservedOp "->"
                  e <- expr
                  return (p, e)

parseLPat = do e <- parsePatExpr
               e' <- parseMaybePat
               return (e:e')

parseMaybePat = try (do {symbol ";"; parseLPat;})
                <|> (do {return [];})

parseCase = do reserved "case"
               e <- expr
               reserved "of"
               symbol "{"
               pes <- parseLPat
               symbol "}"
               return (Case e pes)

parseExprLit = do Lit <$> parseLit

parsePat = try parsePatPair     -- (Pat, Pat)
           <|> parsePatVarOrCons
           <|> parsePatLit      -- lit

parseNonApp = try parsePair    -- (E, E)
              <|> parens expr  -- (E)
              <|> parseLet     -- let x = E in E
              <|> parseIf      -- if E then E else E
              <|> lamAbs       -- \x.E
              <|> parseCase    -- case E of {LPat}
              <|> parseExprLit -- literal
              <|> parseVarOrConst   -- x