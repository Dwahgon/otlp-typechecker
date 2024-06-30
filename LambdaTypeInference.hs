module LambdaTypeInference where

import LambdaTypes
import Data.List(nub, intersect, union, (\\), elemIndex)
import Control.Monad (mapAndUnzipM)

data SimpleType = TVar Id
    | TArr SimpleType SimpleType
    | TCon String
    | TApp SimpleType SimpleType
    | TGen Int
    deriving Eq

type Index  = Int
newtype TI a   = TI (Index -> (a, Index))
type Subst  = [(Id, SimpleType)]
data Assump = Id :>: SimpleType deriving (Eq, Show)

instance Show SimpleType where
   show (TVar i) = i
   show (TCon i) = i
   show (TGen i) = "a" ++ show i
   show (TArr (TVar i) t) = i++" -> "++show t
   show (TArr (TCon i) t) = i++" -> "++show t
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
t |<| t' = TApp t t'
a |<>| b = (TCon "(,)" |<| a) |<| b

infixr 4 @@
(@@)       :: Subst -> Subst -> Subst
s1 @@ s2    = [ (u, apply s1 t) | (u,t) <- s2 ] `union` s1 -- Mudei pra union ao inves de ++ pra remover registros repetidos

as /+/ as' = as' ++ filter compl as
   where
     dom = map (\(i:>:_)->i)
     is = dom as'
     compl (i:>:_) = i `notElem` is
----------------------------
class Subs t where
  apply :: Subst -> t -> t
  tv    :: t -> [Id]

instance Subs SimpleType where
  apply s (TVar u)  =
                    case lookup u s of
                       Just t  -> t
                       Nothing -> TVar u
  apply s (TArr l r) = TArr (apply s l) (apply s r)
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
  tv          = nub . concatMap tv

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
                                 s2 <- mgu (apply s1 r, apply s1 r')
                                 return (s2 @@ s1)
mgu (TArr l r,  TArr l' r') = do s1 <- mgu (l,l')
                                 s2 <- mgu (apply s1 r, apply s1 r')
                                 return (s2 @@ s1)

mgu (t, u) = Nothing

-- This function replaces all TVars in a SimpleType with TGens if 'l' contains TVar
quantify l (TVar i) = case i `elemIndex` l of
   Nothing -> TVar i
   Just i' -> TGen i'
quantify l (TArr a b) = TArr (quantify l a) (quantify l b)
quantify l (TApp a b) = TApp (quantify l a) (quantify l b)
quantify l t = t

unify t t' =  case mgu (t,t') of
    Nothing -> error ("\ntrying to unify:\n" ++ show t ++ "\nand\n" ++ show t'++"\n")
    Just s  -> s

iniCont = ["(,)" :>: TArr (TGen 0) (TArr (TGen 1) (TApp (TApp (TCon "(,)") (TGen 0))
            (TGen 1))), "True" :>: TCon "Bool", "False" :>: TCon "Bool",
            "Just" :>: TArr (TGen 0) (TApp (TCon "Maybe") (TGen 0)), "Nothing" :>: TApp (TCon "Maybe") (TGen 0)]


findTGens (TGen i) = [i]
findTGens (TArr l r) = nub (findTGens l ++ findTGens r)
findTGens (TApp l r) = findTGens (TArr l r)
findTGens t = []

tgenToFresh i = do b <- freshVar
                   return ("a" ++ show i, b)

tgensToFresh [] = return []
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
tiExpr g (If c l r) = do (t, s1) <- tiExpr g c
                         let s' = unify t (TCon "Bool")
                         (t', s2) <- tiExpr (apply (s1@@s') g) l
                         (t'', s3) <- tiExpr (apply (s2@@s1@@s') g) r
                         let s'' = unify (apply s3 t') t''
                         return (apply s'' t', s1@@s2@@s3@@s'@@s'')
tiExpr g (Let (i, e) e') = do (t, s1) <- tiExpr g e
                              let s1g = apply s1 g
                              (t', s2) <- tiExpr (s1g /+/ [i:>:quantify (tv t \\ tv s1g) t]) e'
                              return (t', s2 @@ s1)
tiExpr g (Case e ps) = do (t1, s1) <- tiExpr g e
                          tips <- tiPSExpr (apply s1 g) t1 ps -- [(patternType, expressiontype, subst)]
                          let (tps, tes, ses) = unzip3 tips --([patternType], [expressionType], [subst])
                          let ss = foldl1 (@@) (s1:ses)
                          let sp = unifyAll ss tps
                          let se = unifyAll (sp@@ss) tes
                          let alls = sp @@ se @@ ss
                          return (apply alls (head tes), alls)

unifyAll s [] = s
unifyAll s [t] = s
unifyAll s (t1:t2:ts) = unifyAll (s @@ unify t1 t2) (t2:ts)

tiPExpr g (PVar i) = do b <- freshVar
                        return (b, g /+/ [i:>:b])
tiPExpr g (PLit (LitBool b)) = do t <- tiContext g (show b)
                                  return (t, g)
tiPExpr g (PLit (LitInt i)) = return (TCon "Int", g)
tiPExpr g (PCon i ps) = do (ts, gs) <- mapAndUnzipM (tiPExpr g) ps
                           let gt = g /+/ foldr (/+/) [] gs
                           t <- tiContext gt i
                           b <- freshVar
                           let s = unify t (foldr (-->) b ts)
                           return (apply s b, apply s gt)

tiPSExpr g t [] = return []
tiPSExpr g t ((p, e):xs) = do (t1, g') <- tiPExpr g p
                              let s = unify t t1
                              (t2, s') <- tiExpr (apply s g') e
                              let ss = s @@ s'
                              ts <- tiPSExpr (apply ss g') t xs
                              return ((apply ss t1, apply ss t2, ss):ts)

infer e = runTI (tiExpr iniCont e)
