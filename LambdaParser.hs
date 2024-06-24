import Text.Parsec
import qualified Text.Parsec.Token as L
import Text.Parsec.Language (emptyDef)
import Data.Char
import Data.List(nub, intersect, union)

type Id = String

data Literal = LitInt Integer | LitBool Bool deriving (Show, Eq)

data Pat = PVar Id
    | PLit Literal
    | PCon Id [Pat]
    | PPair Pat Pat
    deriving (Eq, Show)

data Expr = Var Id
    | Const Id
    | App Expr Expr
    | Lam Id Expr
    | Lit Literal
    | Pair Expr Expr
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
expr = chainl1 parseNonApp $ return $ App

isConst (x:xs) = isUpper x
isVar (x:xs) = not (isUpper x)
parseVarOrConst = do i <- identifier
                     return (if (isVar i) then (Var i) else (Const i))

lamAbs = do symbol "\\"
            i <- identifier
            symbol "."
            e <- expr
            return (Lam i e)

parseLitBool = do b <- do {reserved "True"; return True} <|> do {reserved "False"; return False}
                  return (LitBool b)

parseLitInt = do i <- integer
                 return (LitInt i)

parseLit = parseLitBool
           <|> parseLitInt

parseLet = do reserved "let"
              i <- identifier
              reservedOp "="
              e <- expr
              reserved "in"
              e' <- expr
              return (Let (i, e) e')

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

parsePatCons = do c <- identifier
                  p <- parsePats
                  return (if isConst c then PCon c p else undefined)

parsePats = try (do {p <- parsePat; ps <- parsePats; return (p:ps);})
            <|> (do {return ([]);})


parsePatPair = do symbol "("
                  p <- parsePat
                  symbol ","
                  p' <- parsePat
                  symbol ")"
                  return (PPair p p')

parsePatVar = do i <- identifier
                 return (PVar i)

parsePatLit = do l <- parseLit
                 return (PLit l)

parsePatExpr = do p <- parsePat
                  reservedOp "->"
                  e <- expr
                  return (p, e)

parseLPat = do e <- parsePatExpr
               e' <- parseMaybePat
               return (e:e')

parseMaybePat = try (do {symbol ";"; p <- parseLPat; return p;})
                <|> (do {return [];})

parseCase = do reserved "case"
               e <- expr
               reserved "of"
               symbol "{"
               pes <- parseLPat
               symbol "}"
               return (Case e pes)

parseExprLit = do l <- parseLit
                  return (Lit l)

parsePat = parsePatCons         -- Cons Pats
           <|> parsePatPair     -- (Pat, Pat)
           <|> parsePatVar      -- x
           <|> parsePatLit      -- lit

parseNonApp = try parsePair    -- (E, E)
              <|> parens expr  -- (E)
              <|> parseLet     -- let x = E in E
              <|> parseIf      -- if E then E else E
              <|> lamAbs       -- \x.E
              <|> parseCase    -- case E of {LPat}
              <|> parseExprLit -- literal
              <|> parseVarOrConst   -- x

----------------------------------------



data SimpleType = TVar Id
    | TArr SimpleType SimpleType
    | TCon String
    | TApp SimpleType SimpleType
    | TGen Int
    deriving Eq

type Index  = Int
data TI a   = TI (Index -> (a, Index))
type Subst  = [(Id, SimpleType)]
data Assump = Id :>: SimpleType deriving (Eq, Show)

instance Show SimpleType where
   show (TVar i) = i
   show (TCon i) = i
   show (TGen i) = show i
   show (TArr (TVar i) t) = i++" -> "++show t
   show (TArr t t') = "("++show t++")"++"->"++show t'
   show (TApp t t') = show t ++ " " ++ show t'
--------------------------
instance Functor TI where
   fmap f (TI m) = TI (\e -> let (a, e') = m e in (f a, e'))

instance Applicative TI where
   pure a = TI (\e -> (a, e))
   TI fs <*> TI vs = TI (\e -> let (f, e') = fs e; (a, e'') = vs e' in (f a, e''))

instance Monad TI where
--   return x = TI (\e -> (x, e))
   TI m >>= f  = TI (\e -> let (a, e') = m e; TI fa = f a in fa e')

freshVar :: TI SimpleType
freshVar = TI (\e -> let v = "t"++show e in (TVar v, e+1))

runTI (TI m) = let (t, _) = m 0 in t
----------------------------
t --> t' = TArr t t'

infixr 4 @@
(@@)       :: Subst -> Subst -> Subst
s1 @@ s2    = [ (u, apply s1 t) | (u,t) <- s2 ] ++ s1

dom = map (\(i:>:_)->i)

as /+/ as' = as' ++ filter compl as
   where
     is = dom as'
     compl (i:>:_) = notElem i is
----------------------------
class Subs t where
  apply :: Subst -> t -> t
  tv    :: t -> [Id]

instance Subs SimpleType where
  apply s (TVar u)  =
                    case lookup u s of
                       Just t  -> t
                       Nothing -> TVar u
  apply s (TArr l r) =  (TArr (apply s l) (apply s r))
  apply s (TCon t) = TCon t


  tv (TVar u)  = [u]
  tv (TArr l r) = tv l `union` tv r
  tv (TCon t) = [t]


instance Subs a => Subs [a] where
  apply s     = map (apply s)
  tv          = nub . concat . map tv

instance Subs Assump where
  apply s (i:>:t) = i:>:apply s t
  tv (i:>:t) = tv t

------------------------------------
varBind :: Id -> SimpleType -> Maybe Subst
varBind u t | t == TVar u   = Just []
            | u `elem` tv t = Nothing
            | otherwise     = Just [(u, t)]


mgu (TArr l r,  TArr l' r') = do s1 <- mgu (l,l')
                                 s2 <- mgu ((apply s1 r) ,  (apply s1 r'))
                                 return (s2 @@ s1)
mgu (t,        TVar u   )   =  varBind u t
mgu (TVar u,   t        )   =  varBind u t
mgu (TCon tc1, TCon tc2)
   | tc1 == tc2 = Just []
   | otherwise = Nothing
mgu (TApp l r,  TApp l' r') = do s1 <- mgu (l,l')
                                 s2 <- mgu ((apply s1 r) ,  (apply s1 r'))
                                 return (s2 @@ s1)

unify t t' =  case mgu (t,t') of
    Nothing -> error ("\ntrying to unify:\n" ++ (show t) ++ "\nand\n" ++
                      (show t')++"\n")
    Just s  -> s


iniCont = ["(,)" :>: (TArr (TGen 0) (TArr (TGen 1) (TApp (TApp (TCon "(,)") (TGen 0))
            (TGen 1)))), "True" :>: (TCon "Bool"), "False" :>: (TCon "Bool")]

tiContext g i = if l /= [] then t else error ("Undefined: " ++ i ++ "\n")
   where
      l = dropWhile (\(i' :>: _) -> i /= i' ) g
      (_ :>: t) = head l

tiExpr g (Var i) = return (tiContext g i, [])
tiExpr g (App e e') = do (t, s1) <- tiExpr g e
                         (t', s2) <- tiExpr (apply s1 g) e'
                         b <- freshVar
                         let s3 = unify (apply s2 t) (t' --> b)
                         return (apply s3 b, s3 @@ s2 @@ s1)
tiExpr g (Lam i e) = do b <- freshVar
                        (t, s)  <- tiExpr (g/+/[i:>:b]) e
                        return (apply s (b --> t), s)
tiExpr g (Lit (LitInt i)) = do return (TCon "Int", [])
tiExpr g (Lit (LitBool i)) = do return (TCon "Bool", [])
tiExpr g (Const c) = do return (TCon c, [])
tiExpr g (If c l r) = do (t, s1) <- tiExpr g c
                         let s' = unify t (TCon "Bool")
                         (t', s2) <- tiExpr (apply (s1@@s') g) l
                         (t'', s3) <- tiExpr (apply (s2@@s1@@s') g) r
                         let s'' = unify t' t''
                         return (t', s1@@s2@@s3@@s'@@s'')
tiExpr g (Let (i, e) e') = do (t, s1) <- tiExpr g e
                              (t', s2) <- tiExpr ((apply s1 g) /+/ [i:>:t]) e'
                              return (t', s1 @@ s2)

-- case x of
--    Just a -> [a]
--    Nothing -> []
-- unificar x just a e nothing
-- unificar [a] []
-- retornar o tipo [a] []

-- ftv (TVar) = 
-- tiExpr g (Let (i, e) e') = do (t, s1)  <- tiExpr g e
--                               (t', s2) <- tiExpr (apply s1 (g/+/[i:>:])) e'
--                               return (t', s1 @@ s2)

infer e = runTI (tiExpr iniCont e)

parseLambda s = case parseExpr s of
                     Left er -> print er
                     Right e -> (print e >> print (infer e))

main = do putStr "Lambda:"
          e <- getLine
          parseLambda e