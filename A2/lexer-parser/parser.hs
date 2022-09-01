import Lexer
import Data.Either
import Data.List

data MyExpr = Id String | Num Int | MyTrue | MyFalse
            | Add MyExpr MyExpr
            | Sub MyExpr MyExpr
            | Mult MyExpr MyExpr
            | Or MyExpr MyExpr
            | Xor MyExpr MyExpr
            | Implies MyExpr MyExpr
            | And MyExpr MyExpr
            | GrThan MyExpr MyExpr
            | LessThan MyExpr MyExpr
            | Equals MyExpr MyExpr
            | Negate MyExpr
            | Not MyExpr
            | LETBINDING String MyExpr MyExpr
            | IFTHENELSE MyExpr MyExpr MyExpr
            deriving Show


type ParseError = String

-- <factor> ::= <Identifier> | <Const> | (<expr>) | <if> | <let>

parseFactor :: [Token] -> ([Token],Either ParseError MyExpr)
parseFactor (ID _ t:ts) = (ts,Right $ Id t)
parseFactor (CONST _ "TRUE":ts) = (ts,Right MyTrue)
parseFactor (CONST _ "FALSE":ts) = (ts,Right MyFalse)
parseFactor (CONST _ t:ts) = (ts,Right $ Num (read t))
parseFactor t@(RPAREN _ :ts) = (t,Left ("Syntax Error"++":"++show (lineNum (token_posn (head t)))++":"++show (colNum (token_posn (head t)))++" No Start LPAREN "))
parseFactor (LPAREN _:ts) =
    case parseMyExpr ts of
        (ts',r@(Right _)) ->
            case ts' of
               (RPAREN _:ts'') ->  (ts'',r)
               _ -> (ts',Left (error (head ts')))
        (ts',Left m) -> (ts',Left m)
    where
        error t = "Syntax Error"++":"++show (lineNum (token_posn t))++":"++show (colNum (token_posn t))++" missing ) RPAREN "

parseFactor x@(IF _ :xs) = parseIfThenElse x
parseFactor x@(LET _ :xs) = parseLetBinding x


-- <if> ::= if <expr> then <expr> else <expr> fi
parseIfThenElse :: [Token] -> ([Token],Either ParseError MyExpr)
parseIfThenElse (IF _ : xs) =
    case parseMyExpr xs of
        (ts,Right exp) -> extendIf ts exp
        (ts,Left m) -> (ts,Left m)

extendIf :: [Token] -> MyExpr -> ([Token],Either ParseError MyExpr)

extendIf (THEN _ : xs) exp1 =
        case parseMyExpr xs of
            (ts,Right exp2) ->
                case ts of
                    (ELSE _ : ts') ->
                        case parseMyExpr ts' of
                            (ts'',Right exp3) ->
                                case ts'' of
                                    (FI _:ts''') -> (ts''',Right $ IFTHENELSE exp1 exp2 exp3)
                                    _ -> (ts'',Left (error2 ts''))
                            (ts'',Left m) -> (ts'',Left m)
                    _ -> (ts,Left (error1 ts))
            (ts,Left m) -> (ts,Left m)
        where
            error1 xs = "Syntax Error"++":"++show (lineNum (token_posn $ head xs))++":"++show (colNum (token_posn $ head xs))++"TOKEN_TYPE ELSE expected"
            error2 xs = "Syntax Error"++":"++show (lineNum (token_posn $ head xs))++":"++show (colNum (token_posn $ head xs))++"TOKEN_TYPE FI expected"

extendIf xs exp1 = (xs,Left ("Syntax Error"++":"++show (lineNum (token_posn $ head xs))++":"++show (colNum (token_posn $ head xs))++"TOKEN_TYPE THEN expected"))

-- <let> ::= let <id> <assign> <expr> in <expr> end
parseLetBinding :: [Token] -> ([Token],Either ParseError MyExpr)
parseLetBinding (LET _ : xs) =
    case xs of
        ID _ n : xs' ->
            case xs' of
                ASSIGN _ : xs'' ->
                    case parseMyExpr xs'' of
                        (ts,Right exp) ->
                            case ts of
                                IN _ : ts' ->
                                    case parseMyExpr ts' of
                                        (ts'',Right exp') ->
                                            case ts'' of
                                                END _ : ts''' -> (ts''',Right (LETBINDING n exp exp'))
                                                _ -> (ts'',Left (errorEND (head ts'')))
                                        (ts'',Left m) -> (ts'',Left m)
                                _ -> (ts,Left (errorIN (head ts)))
                        (ts,Left m) -> (ts,Left m)
                _ -> (xs',Left (errorASSIGN (head xs')))
        _ -> (xs,Left (errorID (head xs)))
    where
        errorID t = "Syntax Error"++":"++show (lineNum (token_posn t))++":"++show (colNum (token_posn t))++" TOKEN_TYPE ID expected "
        errorASSIGN t = "Syntax Error"++":"++show (lineNum (token_posn t))++":"++show (colNum (token_posn t))++" TOKEN_TYPE ASSIGN expected "
        errorIN t = "Syntax Error"++":"++show (lineNum (token_posn t))++":"++show (colNum (token_posn t))++" TOKEN_TYPE IN expected "
        errorEND t = "Syntax Error"++":"++show (lineNum (token_posn t))++":"++show (colNum (token_posn t))++" TOKEN_TYPE END expected "



-- <term> ::= <factor> | <term> and <factor> | <term> * <factor>

parseTerm :: [Token] -> ([Token],Either ParseError MyExpr)
parseTerm xs =
    case parseFactor xs of
        (ts,Right factor) -> extendTerm ts factor
        (ts,Left m) -> (ts,Left m)

extendTerm :: [Token] -> MyExpr -> ([Token],Either ParseError MyExpr)

extendTerm (AND _ : xs) expr =
    case parseFactor xs of
        (ts,Right term) -> extendTerm ts (And expr term)
        (ts,Left m) -> (ts,Left m)

extendTerm (TIMES _ : xs) expr =
    case parseFactor xs of
        (ts,Right term) -> extendTerm ts (Mult expr term)
        (ts,Left m) -> (ts,Left m)

extendTerm xs term = (xs,Right term)


-- <expr> ::= <term> | <expr>+<term> | <expr>-<term> | <expr> or <term> | <expr> xor <term> | <expr> implies <expr> 
--            | <expr> < <expr> | <expr> > <expr> | <expr> == <expr> | ~<factor> | not <factor>

parseMyExpr :: [Token] -> ([Token],Either ParseError MyExpr)
parseMyExpr (NEGATE _ : xs) =
    case parseFactor xs of
        (ts,Right factor) -> (ts,Right (Negate factor))
        (ts,Left m) -> (ts,Left m)
parseMyExpr (NOT _ : xs) =
    case parseFactor xs of
        (ts,Right factor) -> (ts,Right (Not factor))
        (ts,Left m) -> (ts,Left m)
parseMyExpr xs =
    case parseTerm xs of
        (ts,Right term) -> extendExpr ts term
        (ts,Left m) -> (ts,Left m)

extendExpr :: [Token] -> MyExpr -> ([Token],Either ParseError MyExpr)

extendExpr (PLUS _ : xs) term =
    case parseTerm xs of
        (ts,Right term') -> extendExpr ts (Add term term')
        (ts,Left m) -> (ts,Left m)

extendExpr (MINUS _ : xs) term =
    case parseTerm xs of
        (ts,Right term') -> extendExpr ts (Sub term term')
        (ts,Left m) -> (ts,Left m)

extendExpr (XOR _ : xs) term =
    case parseTerm xs of
        (ts,Right term') -> extendExpr ts (Xor term term')
        (ts,Left m) -> (ts,Left m)

extendExpr (OR _ : xs) term =
    case parseTerm xs of
        (ts,Right term') -> extendExpr ts (Or term term')
        (ts,Left m) -> (ts,Left m)

extendExpr (IMPLIES _ : xs) expr =
    case parseMyExpr xs of
        (ts,Right expr') -> extendExpr ts (Implies expr expr')
        (ts,Left m) -> (ts,Left m)

extendExpr (LESSTHAN _ : xs) expr =
    case parseMyExpr xs of
        (ts,Right expr') -> extendExpr ts (LessThan expr expr')
        (ts,Left m) -> (ts,Left m)

extendExpr (GREATERTHAN _ : xs) expr =
    case parseMyExpr xs of
        (ts,Right expr') -> extendExpr ts (GrThan expr expr')
        (ts,Left m) -> (ts,Left m)

extendExpr (EQUALS _ : xs) expr =
    case parseMyExpr xs of
        (ts,Right expr') -> extendExpr ts (Equals expr expr')
        (ts,Left m) -> (ts,Left m)

extendExpr xs expr =
    case xs of
        (ID _ _: ts) -> (ts , Left (error (head xs)))
        (CONST _ _: ts) -> (ts , Left (error (head xs)))
        _ -> (xs,Right expr)
    where
        error t = "Syntax Error"++":"++show (lineNum (token_posn t))++":"++show (colNum (token_posn t))++" Bin Operator Expected "

lastTokenPosn :: [Token] -> AlexPosn
lastTokenPosn ts = token_posn (last ts)

preOrderTraversal :: [Token] -> [String]
preOrderTraversal xs =
    case parseMyExpr xs of
        (ts,Left m) -> error m
        ([],Right _) ->
            let
                p = lastTokenPosn xs
            in
                error ("Syntax Error" ++ ":" ++ show (lineNum p) ++ ":" ++ show (colNum p) ++ " EOF_TOKEN NOT PRESENT ")
        ([EOF _],Right exp) -> preOrder exp

preOrder :: MyExpr -> [String]
preOrder exp =
    case exp of
                MyTrue -> ["CONST" ++ " " ++ show MyTrue]
                MyFalse -> ["CONST" ++ " " ++ show MyFalse]
                Id s -> ["Id" ++ " " ++  s]
                Num n -> ["Num" ++ " " ++ show n]
                Negate exp' -> "Negate":preOrder exp'
                Not exp' -> "Not":preOrder exp'
                Add exp' exp'' -> "Add":preOrder exp'++preOrder exp''
                Sub exp' exp'' -> "Sub":preOrder exp'++preOrder exp''
                Mult exp' exp'' -> "Mult":preOrder exp'++preOrder exp''
                Or exp' exp'' -> "Or":preOrder exp'++preOrder exp''
                Xor exp' exp'' -> "Xor":preOrder exp'++preOrder exp''
                Implies exp' exp'' -> "Implies":preOrder exp'++preOrder exp''
                And exp' exp'' -> "And":preOrder exp'++preOrder exp''
                Equals exp' exp'' -> "Equals":preOrder exp'++preOrder exp''
                GrThan exp' exp'' -> "GrThan":preOrder exp'++preOrder exp''
                LessThan exp' exp'' -> "LessThan":preOrder exp'++preOrder exp''
                LETBINDING s exp' exp'' -> "LETBINDING":["Id" ++ " " ++ s] ++preOrder exp'++preOrder exp''
                IFTHENELSE exp' exp'' exp''' -> "IFTHENELSE":preOrder exp'++preOrder exp''++preOrder exp'''


main :: IO ()
main = do
    s <- getLine
    let xs = scanTokens s
    putStrLn (show xs ++ "\n" ++ show (preOrderTraversal xs))
























