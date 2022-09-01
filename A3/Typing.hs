module Typing (getType) where
import Lexer
import Parser
import Ast


type Env = [(Id,Type)]

-- environment extend
extendEnv :: (Id,Type) -> Env -> Env
extendEnv = (:)

-- variable lookup in the env
lookUp :: Id -> Env -> Maybe Type
lookUp _ [] = Nothing
lookUp x ((y,t):es) =
    if x == y then Just t
    else lookUp x es

type TypeError = String
getType :: Expr -> Env -> Either TypeError Type

getType (BinExpr op e1 e2) env
    | op == Plus || op == Minus || op == Times =
        case getType e1 env of
            Right IntType ->
                case getType e2 env of
                    Right IntType -> Right IntType
                    _ -> Left $ "TypeMisMatchException At " ++ show op  ++  " Int Expected"
            _ -> Left $ "TypeMisMatchException At " ++ show op  ++  " Int Expected"
    | op == Equals =
        case getType e1 env of
            Right t ->
                case getType e2 env of
                    Right t' -> if t == t' then Right BoolType
                                else Left "TypeMisMatchException"
                    Left m -> Left m
            Left m -> Left m
    | op == LessThan || op == GreaterThan =
        case getType e1 env of
            Right IntType ->
                case getType e2 env of
                    Right IntType -> Right BoolType
                    _ -> Left $ "TypeMisMatchException At " ++ show op  ++  " Int Expected"
            _ -> Left $ "TypeMisMatchException At " ++ show op  ++  " Int Expected"
    | op == And || op == Or || op == Xor =
        case getType e1 env of
            Right BoolType ->
                case getType e2 env of
                    Right BoolType -> Right BoolType
                    _ -> Left $ "TypeMisMatchException At " ++ show op ++ " Bool Expected"
            _ -> Left $ "TypeMisMatchException At " ++ show op ++ " Bool Expected"

getType (UnExpr Not e) env =
    case getType e env of
        Right BoolType -> Right BoolType
        _ -> Left $ "TypeMisMatchException " ++ show Not ++ " Bool Expected"

getType (UnExpr Negate e) env =
    case getType e env of
        Right IntType -> Right IntType
        _ -> Left $ "TypeMisMatchException " ++ show Negate ++ " Int Expected"

getType (Ite e1 e2 e3) env =
    case getType e1 env of
        Right BoolType ->
            case getType e2 env of
                Right t ->
                    case getType e3 env of
                        Right t' -> if t == t' then Right t
                                    else Left "TypeMisMatchException"
                        Left m -> Left m
                Left m -> Left m
        Left m -> Left m
        Right _ -> Left "TypeMisMatchException in \'if then else\' : Bool Expected"

getType (Let (Decl x e1) e2) env =
    case getType e1 env of
        Right t ->
            case getType e2 (extendEnv (x,t) env) of
                Right t' -> Right t'
                Left m -> Left m
        Left m -> Left m

getType (BoolConst _) env = Right BoolType
getType (IntConst _) env = Right IntType
getType (VarExpr x) env =
    case lookUp x env of
        Nothing -> Left $ "Variable " ++ x ++ " w/o a type"
        Just t -> Right t

getType (AppExp e1 e2) env =
    case getType e2 env of
        Right t ->
            case getType e1 env of
                Right (Arrow t t') -> Right t'
                Left m -> Left m
                Right _ -> Left "TypeMisMatchException : Function Application"
        Left m -> Left m

getType (Fn x t e) env =
    case getType e (extendEnv (x,t) env) of
        Right t' -> Right $ Arrow t t'
        Left m -> Left m

getType (FunExp name y t t' e) env =
        case getType e (extendEnv (name,Arrow t t') (extendEnv (y,t) env)) of
            Right t' -> Right (Arrow t t')
            _ -> Left "TypeMisMatchException : Function Value Type MisMatch"    -- function value type mismatch


-- TODO
