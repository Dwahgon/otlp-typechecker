import Text.Parsec
import qualified Text.Parsec.Token as L
import Text.Parsec.Language (emptyDef)

type Id = String

data Pat = PVar Id
    | PLit Literal
    | PCon Id [Pat]
    deriving (Eq, Show)

data Literal = LitInt Integer | LitBool Bool deriving (Show, Eq)

data Expr = Var Id
    | Const Id
    | App Expr Expr
    | Lam Id Expr
    | Lit Literal
    | If Expr Expr Expr
    | Case Expr [(Pat, Expr)]
    | Let (Id, Expr) Expr
    deriving (Eq, Show)

lingDef = emptyDef
          { L.commentStart = "{-"
           ,L.commentEnd   = "-}"
           ,L.commentLine  = "--"
           ,L.identStart   = letter
           ,L.identLetter  = letter
           ,L.reservedNames = ["let", "in", "if", "then", "else", "case", "of"]
           ,L.reservedOpNames = ["="]
          }  

lexical = L.makeTokenParser lingDef


symbol     = L.symbol lexical
parens     = L.parens lexical
identifier = L.identifier lexical
reserved   = L.reserved lexical
reservedOp = L.reservedOp lexical

--------- Parser -----------------
parseExpr = runParser expr [] "lambda-calculus"

expr :: Parsec String u Expr
expr = chainl1 parseNonApp $ return $ App

var = do i <- identifier
         return (Var i)

lamAbs = do symbol "\\"
            i <- identifier
            symbol "."
            e <- expr
            return (Lam i e)

parseLet = do reserved "let"
              i <- identifier
              reservedOp "="
              e <- expr
              reserved "in"
              e' <- expr
              return (Let i e e')

parseIf = do reserved "if"
             c <- expr
             reserved "then"
             e <- expr
             reserved "else"
             e' <- expr
             return (If c e e')

parsePair = do symbol "("
               e <- expr
               symbol ","
               e' <- expr
               symbol ")"
               return (Pair e e')

parsePatExpr

parseCase = do reserved "case"
               e <- expr
               reserved "of"
               symbol "{"
               pes <- parsePatExpr
               symbol "}"
               return (Case Expr pes)


parseNonApp = try parsePair
              <|> parens expr      -- (E)
              <|> parseLet     -- let x = E in E
              <|> parseIf      -- if E then E else E
              <|> lamAbs       -- \x.E
              <|> var          -- x

----------------------------------------
parseLambda s = case parseExpr s of
                     Left er -> print er
                     Right e -> (print e)

main = do putStr "Lambda:"
          e <- getLine
          parseLambda e