import Ast
import Lexer
import Parser
import Typing 
import Evaluator

-- returns the pre-order traversal of Ast 
mainPreOrder :: FilePath -> IO ()
mainPreOrder = preOrderAST


-- **to be called only if lexical analyser and syntactical analyser succeeds** --
mainTypeChecker :: FilePath -> IO ()
mainTypeChecker path = do
    s <- readFile path
    case getType (parser $ scanTokens s) [] of
        Left m ->
            do
                print m
        Right t ->
            do
                print t

-- **to be called only if type checker succeeds** --
mainEvalExpr :: FilePath -> IO ()
mainEvalExpr path = do 
    s <- readFile path
    print (eval ((parser.scanTokens) s) [])                


