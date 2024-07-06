module LambdaTypes where

type Id = String

data Literal = LitInt Integer | LitBool Bool | LitChar Char deriving (Show, Eq)

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