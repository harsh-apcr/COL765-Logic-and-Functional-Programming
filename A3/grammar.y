{
module Parser where
import Ast
import Lexer
import qualified Control.Exception as Exc
import System.IO
}

%name parser
%tokentype { Token }
%error { parseError }

%token
       ";"     { EOF $$ }
       "("     { LPAREN $$ }
       ")"     { RPAREN $$ }
       -- int ops
       "+"     { PLUS $$ }
       "-"     { MINUS $$ }
       "*"     { TIMES $$ }
       "~"     { NEGATE $$ }
       "="     { EQUALS $$ }
       "<"     { LESSTHAN $$ }
       ">"     { GREATERTHAN $$ }
       -- bool ops
       "!"     { NOT $$ }
       "&&"    { AND $$ }
       "||"    { OR $$ }
       "^"     { XOR $$ }
       --"=>"    { IMPLIES $$ }
       -- ite
       "if"    { IF $$ }
       "then"  { THEN $$ }
       "else"  { ELSE $$ }
       "fi"    { FI $$ }
       -- let
       "let"   { LET $$ }
       ":="    { ASSIGN $$ }
       "in"    { IN $$ }
       "end"   { END $$ }
       -- function support
       "fn"    { FN $$ }
       "::"    { COLON $$ }
       "->"    { RIGHTARROW $$ } 
       "fun"   { FUN $$ }
       "=>"    { IMPLY $$ }
       "int"   { INT $$ }
       "bool"  { BOOL $$ } 
       -- atoms
       "false" { FALSE $$ }
       "true"  { TRUE $$ }
       int     { CONST $$ }
       var     { ID $$ }


%nonassoc ">" "<" "="
%left "+" "-"
%left "*"
%left "^" "||" "&&"
%right "!" "~"

%%

Start
    : Expr ";"				     { $1 }

Decl
    : var ":=" Expr                          { Decl $1 $3 }

Expr
    : "(" Expr ")"                           { $2 }

    -- int ops
    | "~" Expr                               { UnExpr Negate $2 }
    | Expr "+" Expr                          { BinExpr Plus $1 $3 }
    | Expr "-" Expr                          { BinExpr Minus $1 $3 }
    | Expr "*" Expr                          { BinExpr Times $1 $3 }
    | Expr "=" Expr                          { BinExpr Equals $1 $3 }
    | Expr "<" Expr                          { BinExpr LessThan $1 $3 }
    | Expr ">" Expr                          { BinExpr GreaterThan $1 $3 }

    -- bool ops
    | "!" Expr                               { UnExpr Not $2 }
    | Expr "&&" Expr                         { BinExpr And $1 $3 }
    | Expr "||" Expr                         { BinExpr Or $1 $3 }
    | Expr "^" Expr                          { BinExpr Xor $1 $3 }
    -- | Expr "=>" Expr                         { BinExpr Implies $1 $3 }

    -- specials
    | "let" Decl "in" Expr "end"             { Let $2 $4 }
    | "if" Expr "then" Expr "else" Expr "fi" { Ite $2 $4 $6 }

    -- atom
    | "false"                                { BoolConst False }
    | "true"                                 { BoolConst True }
    | int                                    { IntConst $1 }
    | var                                    { VarExpr $1 }

    -- function support
    | "(" Expr Expr ")"                      { AppExp $2 $3 }
    | "fn" "(" var "::" Type ")" "=>" Expr "end" { Fn $3 $5 $8 }
    | "fun" var "(" var "::" Type ")" "::" Type "=>" Expr "end" { FunExp $2 $4 $6 $9 $11 }

Type 
    : Type "->" Type                         { Arrow $1 $3 }
    | "int"                                  { IntType }
    | "bool"                                 { BoolType }

{

parseError [] = error $ "Syntax Error in the last token"
parseError (x:xs) = error $ "Syntax Error: " ++ (show x)

preOrder :: Expr -> [String]
preOrder exp =
    case exp of
                BoolConst True -> ["BoolConst" ++ " " ++ "True"]
                BoolConst False -> ["BoolConst" ++ " " ++ "False"]
                VarExpr s -> ["VarExpr" ++ " " ++  s]
                IntConst n -> ["IntConst" ++ " " ++ show n]
                UnExpr Negate exp' -> "Negate":preOrder exp'
                UnExpr Not exp' -> "Not":preOrder exp'
                BinExpr Plus exp' exp'' -> "Plus":preOrder exp'++preOrder exp''
                BinExpr Minus exp' exp'' -> "Minus":preOrder exp'++preOrder exp''
                BinExpr Times exp' exp'' -> "Times":preOrder exp'++preOrder exp''
                BinExpr And exp' exp'' -> "And":preOrder exp'++preOrder exp''
                BinExpr Or exp' exp'' -> "Or":preOrder exp'++preOrder exp''
                BinExpr Xor exp' exp'' -> "Xor":preOrder exp'++preOrder exp''
            --    Implies exp' exp'' -> "Implies":preOrder exp'++preOrder exp''
                BinExpr Equals exp' exp'' -> "Equals":preOrder exp'++preOrder exp''
                BinExpr GreaterThan exp' exp'' -> "GrThan":preOrder exp'++preOrder exp''
                BinExpr LessThan exp' exp'' -> "LessThan":preOrder exp'++preOrder exp''
                Let (Decl s exp') exp'' -> "Let":["VarExpr" ++ " " ++ s] ++preOrder exp'++preOrder exp''
                Ite exp' exp'' exp''' -> "Ite":preOrder exp'++preOrder exp''++preOrder exp'''
                AppExp exp' exp'' -> "AppExp":preOrder exp'++preOrder exp''
                Fn s _ exp' -> "Fn":["VarExpr" ++ " " ++ s]++preOrder exp'
                FunExp name y _ _ exp' -> "Fun":["VarExpr" ++ name]++["VarExpr" ++ y]++preOrder exp'

preOrderAST :: FilePath -> IO ()
preOrderAST path = do
    s <- readFile path
    tkls <- Exc.try (return (scanTokens s))
    case tkls of
        Left e -> do putStrLn (show (e::Exc.SomeException))
        Right ts ->
            do 
                exp <- Exc.try (return (parser ts))
                case exp of 
                    Left e -> do putStrLn (show (e::Exc.SomeException))
                    Right expr -> do print (preOrder expr)
    
}
