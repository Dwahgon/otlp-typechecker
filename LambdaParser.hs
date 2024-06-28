import Text.Parsec
import qualified Text.Parsec.Token as L
import Text.Parsec.Language (emptyDef)
import Data.Char
import Data.List(nub, intersect, union, (\\), elemIndex)
import Debug.Trace
import Control.Monad

type Id = String

data Literal = LitInt Integer | LitBool Bool deriving (Show, Eq)

data Pat = PVar Id
    | PLit Literal
    | PCon Id [Pat]
    deriving (Eq, Show)

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
               return (App (App (Const "(,)") e) e')

parsePats = try (do {p <- parsePat; ps <- parsePats; return (p:ps);})
            <|> (do {return ([]);})

parsePatVarOrCons = do c <- identifier
                       if isConst c then
                        do p <- parsePats
                           return (PCon c p)
                       else return (PVar c)

-- parsePatCons = do c <- identifier
--                   p <- parsePats
--                   return (if isConst c then PCon c p else undefined)


parsePatPair = do symbol "("
                  p <- parsePat
                  symbol ","
                  p' <- parsePat
                  symbol ")"
                  return (PCon "(,)" [p, p'])

-- parsePatVar = do i <- identifier
--                  return (PVar i)

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
   show (TGen i) = "a" ++ show i
   show (TArr (TVar i) t) = i++" -> "++show t
   show (TArr t t') = "("++show t++")"++"->"++show t'
   show (TApp (TApp (TCon "(,)") a) b) = "(" ++ show a ++ ", " ++ show b ++ ")"
   show (TApp (TVar i) t') = i ++ " " ++ show t'
   show (TApp (TCon i) t') = i ++ " " ++ show t'
   show (TApp t t') = "(" ++ show t ++ ") " ++ show t'
--------------------------
instance Functor TI where
   fmap f (TI m) = TI (\e -> let (a, e') = m e in (f a, e'))

instance Applicative TI where
   pure a = TI (\e -> (a, e))
   TI fs <*> TI vs = TI (\e -> let (f, e') = fs e; (a, e'') = vs e' in (f a, e''))

instance Monad TI where
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
  apply s (TApp l r) = TApp (apply s l) (apply s r)
  apply s (TCon t) = TCon t
  apply s (TGen i) = case lookup ("a" ++ show i) s of
                       Just t -> t
                       Nothing -> TGen i


  tv (TVar u)  = [u]
  tv (TArr l r) = tv l `union` tv r
  tv (TApp l r) = tv l `union` tv r
  tv (TCon t) = []
  tv (TGen i) = []


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

genBind i t | t == TGen i = Just []
            | ("a" ++ show i) `elem` tv t = Nothing
            | otherwise = Just [("a" ++ show i, t)]


mgu (t,        TVar u   )   =  varBind u t
mgu (TVar u,   t        )   =  varBind u t
mgu (TCon tc1, TCon tc2)
   | tc1 == tc2 = Just []
   | otherwise = Nothing
mgu (TGen i, t) = genBind i t
mgu (t, TGen i) = genBind i t
mgu (TApp l r,  TApp l' r') = do s1 <- mgu (l,l')
                                 s2 <- mgu ((apply s1 r) ,  (apply s1 r'))
                                 return (s2 @@ s1)
mgu (TArr l r,  TArr l' r') = do s1 <- mgu (l,l')
                                 s2 <- mgu ((apply s1 r) ,  (apply s1 r'))
                                 return (s2 @@ s1)
mgu (t, u) = Nothing

-- This function replaces all TVars in a SimpleType with TGens if 'l' contains TVar
quantify l (TVar i) = case i `elemIndex` l of
   Nothing -> TVar i
   Just i' -> TGen i'
quantify l (TArr a b) = TArr (quantify l a) (quantify l b)
quantify l (TApp a b) = TApp (quantify l a) (quantify l b)
quantify l t = t
-- quantify' l t = trace ("quantify l=" ++ show l ++ " t=" ++ show t ++ " = " ++ show (quantify l t)) (quantify l t)

unify t t' =  case mgu (t,t') of
    Nothing -> error ("\ntrying to unify:\n" ++ (show t) ++ "\nand\n" ++
                      (show t')++"\n")
    Just s  -> s

iniCont = ["(,)" :>: (TArr (TGen 0) (TArr (TGen 1) (TApp (TApp (TCon "(,)") (TGen 0))
            (TGen 1)))), "True" :>: (TCon "Bool"), "False" :>: (TCon "Bool")]


findTGens (TGen i) = [i]
findTGens (TArr l r) = nub (findTGens l ++ findTGens r)
findTGens (TApp l r) = findTGens (TArr l r)
findTGens t = []

tgenToFresh i = do b <- freshVar
                   return ("a" ++ show i, b)

tgensToFresh ([]) = return ([])
tgensToFresh (x:xs) = do f <- tgenToFresh x
                         fs <- tgensToFresh xs
                         return (f:fs)

instanceGens t = do fs <- tgensToFresh (findTGens t)
                    return (apply fs t)

tiContext g i = if l /= [] then instanceGens t else error ("Undefined: " ++ i ++ "\n")
   where
      l = dropWhile (\(i' :>: _) -> i /= i' ) g
      (_ :>: t) = head l

tiExpr g (Lit (LitBool b)) = do t <- tiContext g (show b)
                                return (t, []) -- True: Bool, False: Bool
tiExpr g (Const c) = do t <- tiContext g c
                        return (t, []) --- Cons
tiExpr g (Var i) = do t <- tiContext g i
                      return (t, []) -- x: t
tiExpr g (Lit (LitInt i)) = return (TCon "Int", []) -- 123: Int
tiExpr g (App e e') = do (t, s1) <- tiExpr g e -- e e': t
                         (t', s2) <- tiExpr (apply s1 g) e'
                         b <- freshVar
                         let s3 = unify (apply s2 t) (t' --> b)
                         return (apply s3 b, s3 @@ s2 @@ s1)
tiExpr g (Lam i e) = do b <- freshVar -- \x.e: b->t
                        (t, s)  <- tiExpr (g/+/[i:>:b]) e
                        return (apply s (b --> t), s)
-- tiExpr g (If c l r) = trace ("let g=" ++ show g ++ " i=" ++ show i ++ " e=" ++ show e ++ " e'" ++ show e') (do (t, s1) <- tiExpr g c
--                                                                                                                let s' = unify t (TCon "Bool")
--                                                                                                                (t', s2) <- tiExpr (apply (s1@@s') g) l
--                                                                                                                (t'', s3) <- tiExpr (apply (s2@@s1@@s') g) r
--                                                                                                                let s'' = unify (apply s3 t') t''
--                                                                                                                return (apply s'' t', s1@@s2@@s3@@s'@@s''))
tiExpr g (If c l r) = do (t, s1) <- tiExpr g c
                         let s' = unify t (TCon "Bool")
                         (t', s2) <- tiExpr (apply (s1@@s') g) l
                         (t'', s3) <- tiExpr (apply (s2@@s1@@s') g) r
                         let s'' = unify (apply s3 t') t''
                         return (apply s'' t', s1@@s2@@s3@@s'@@s'')
-- tiExpr g (Let (i, e) e') = trace ("let g=" ++ show g ++ " i=" ++ show i ++ " e=" ++ show e ++ " e'" ++ show e') (do (t, s1) <- tiExpr g e
--                                                                                                                     let s1g = apply s1 g
--                                                                                                                     (t', s2) <- tiExpr (s1g /+/ [i:>:quantify' (tv s1g \\ tv t) t]) e'
--                                                                                                                     return (t', s1 @@ s2))
tiExpr g (Let (i, e) e') = do (t, s1) <- tiExpr g e
                              let s1g = apply s1 g
                              (t', s2) <- tiExpr (s1g /+/ [i:>:quantify (tv t \\ tv s1g) t]) e'
                              return (t', s1 @@ s2)
tiExpr g (Case e ps) = do (t1, s1) <- tiExpr g e
                          tips <- tiPSExpr (apply s1 g) ps -- [(patternType, (expressiontype, subst))]
                          let (tps, tse) = unzip tips --([patternType], [(expressionType, subst)])
                          let (tes, ses) = unzip tse -- ([expression], [subst])
                          let ss = foldl1 (@@) ([s1] ++ ses)
                          let sp = unifyAll ss (t1:tps)
                          let se = unifyAll (sp@@ss) tes
                          return (apply se (head tes), se)

unifyAll s [] = s
unifyAll s [t] = s
unifyAll s (t1:t2:ts) = unifyAll (s @@ (unify t1 t2)) (t2:ts)

-- PVar Id
-- PLit Literal
-- PCon Id [Pat]

tiPExpr g (PVar i) = do b <- freshVar
                        return (b, g /+/ [i:>:b])
tiPExpr g (PLit (LitBool b)) = do t <- tiContext g (show b)
                                  return (t, g)
tiPExpr g (PLit (LitInt i)) = return (TCon "Int", g)
tiPExpr g (PCon i ps) = do (ts, gs) <- mapAndUnzipM (tiPExpr g) ps
                           let gt = g `union` (foldr1 `union` gs)
                           t <- tiContext gt i
                           b <- freshVar
                           let s = unify t (foldr (-->) b ts)
                           return (apply s t, gt)

tiPSExpr g [] = return ([])
tiPSExpr g ((p, e):xs) = do (t1, g') <- tiPExpr g p
                            (t2, s) <- tiExpr g' e
                            ts <- tiPSExpr (apply s g') xs
                            return ((apply s t1, (t2, s)):ts)


-- \x.let f = (\y.(x,y)) in (f True, f 1)
-- case x of
--    Just a -> [a]
--    Nothing -> []
-- unificar x just a e nothing
-- unificar [a] []
-- retornar o tipo [a] []
-- (\x.let f = (\y.(x,y)) in (case f True of {(x, True) -> 1})) 3

-- case 1 of {False -> 1; 2 -> 2}
-- case 1 of {False -> 1; 2 -> 2}

infer e = runTI (tiExpr iniCont e)

parseLambda s = case parseExpr s of
                     Left er -> print er
                     Right e -> (print e >> print (infer e))

main = do putStr "Lambda:"
          e <- getLine
          parseLambda e