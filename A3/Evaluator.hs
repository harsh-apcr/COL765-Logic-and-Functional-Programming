module Evaluator (eval) where

import Ast
import Lexer
import Parser
import Typing

type ExprEnv = [(Id,Expr)]
extendExprEnv :: (Id,Expr) -> [(Id,Expr)] -> [(Id,Expr)]
extendExprEnv = (:)

lookUpVar :: Id -> ExprEnv -> Maybe Expr
lookUpVar _ [] = Nothing
lookUpVar x ((y,e):es) =
        if x == y then Just e
        else lookUpVar x es

eval :: Expr -> ExprEnv -> Expr

eval (BinExpr binop e1 e2) eenv =
    let
        v1 = eval e1 eenv
        v2 = eval e2 eenv
    in
        case v1 of
            IntConst i1 ->
                case v2 of
                    IntConst i2 ->
                        case binop of
                            Plus -> IntConst (i1+i2)
                            Minus -> IntConst (i1-i2)
                            Times -> IntConst (i1*i2)
                            Equals -> BoolConst (i1==i2)
                            LessThan -> BoolConst (i1<i2)
                            GreaterThan -> BoolConst (i1>i2)
            BoolConst b1 ->
                case v2 of
                    BoolConst b2 ->
                        case binop of
                            Equals -> BoolConst (b1==b2)
                            And -> BoolConst (b1&&b2)
                            Or -> BoolConst (b1||b2)
                            Xor -> BoolConst (b1/=b2)

eval (UnExpr unop e) eenv =
    case eval e eenv of
        IntConst x -> IntConst (-x)
        BoolConst b -> BoolConst (not b)


eval (Ite (BoolConst True) t1 _) eenv = eval t1 eenv
eval (Ite (BoolConst False) _ t0) eenv = eval t0 eenv
eval (Ite t t1 t0) eenv = eval (Ite (eval t eenv) t1 t0) eenv

eval (BoolConst b) _ = BoolConst b
eval (IntConst i) _ = IntConst i

eval (VarExpr x) eenv =
    case lookUpVar x eenv of
        Just e -> e
        _ -> error $ "Variable " ++ x ++ " not defined"

eval (Let (Decl x e1) e2) eenv = eval e2 (extendExprEnv (x,eval e1 eenv) eenv)

eval (AppExp e1 e2) eenv = apply (eval e1 eenv) (eval e2 eenv) eenv

eval fn@(Fn {}) _ = fn
eval fun@(FunExp {}) _ = fun

apply :: Expr -> Expr -> ExprEnv -> Expr

apply (Fn x _ e1) e2 eenv = eval e1 (extendExprEnv (x,eval e2 eenv) eenv)
apply (FunExp name y t _ e1) e2 eenv = eval e1 (extendExprEnv (name,Fn y t e1) (extendExprEnv (y,eval e2 eenv) eenv))

-- TODO
