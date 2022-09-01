module Ast where

type Id = String

data VarDecl = Decl Id Expr
        deriving (Eq,Show)

data UnOp = Negate | Not
        deriving (Eq,Show)

data BinOp = Plus | Minus | Times | Equals | LessThan | GreaterThan | And | Or | Xor 
        deriving (Eq,Show)

data Type = IntType | BoolType | Arrow Type Type
        deriving (Eq,Show)


data Expr =
             BinExpr BinOp Expr Expr
           | UnExpr UnOp Expr
           | Ite Expr Expr Expr
           | Let VarDecl Expr
           | BoolConst Bool
           | IntConst Integer
           | VarExpr Id
           | AppExp Expr Expr
           | Fn Id Type Expr
           | FunExp Id Id Type Type Expr
        deriving (Eq,Show)

