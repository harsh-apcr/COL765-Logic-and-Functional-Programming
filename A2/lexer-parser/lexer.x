{
module Lexer where
import Data.Maybe
}

%wrapper "posn"

$eol = [\n]
$digit = 0-9
$alpha = [a-zA-Z]

tokens :-
    -- whitespace insensitive
    $eol                            ;
    $white+                         ;
    -- syntax
    let                             {tok(\p s -> LET p)}
    TRUE                            {tok(\p s -> CONST p s)}
    FALSE                           {tok(\p s -> CONST p s)}
    in                              {tok(\p s -> IN p)}
    end                             {tok(\p s -> END p)}
    if                              {tok(\p s -> IF p)}
    then                            {tok(\p s -> THEN p)}
    else                            {tok(\p s -> ELSE p)}
    fi                              {tok(\p s -> FI p)}
    [\~]                            {tok(\p s -> NEGATE p)}    
    [\+]                            {tok(\p s -> PLUS p)}
    [\-]                            {tok(\p s -> MINUS p)}
    [\*]                            {tok(\p s -> TIMES p)}
    \==                             {tok(\p s -> EQUALS p)}
    \=                              {tok(\p s -> ASSIGN p)}
    \<                              {tok(\p s -> LESSTHAN p)}
    \>                              {tok(\p s -> GREATERTHAN p)}
    NOT                             {tok(\p s -> NOT p)}
    AND                             {tok(\p s -> AND p)}
    OR                              {tok(\p s -> OR p)}
    XOR                             {tok(\p s -> XOR p)}
    IMPLIES                         {tok(\p s -> IMPLIES p)}
    \(                              {tok(\p s -> LPAREN p)}
    \)                              {tok(\p s -> RPAREN p)}
    $digit+                         {tok(\p s -> CONST p s)}
    $alpha [$alpha]*                {tok(\p s -> ID p s)}
    [\;]                            {tok(\p s -> EOF p)}                              
    






{
tok f p s = f p s
data Token = 
    NEGATE AlexPosn |    
    PLUS AlexPosn |
    MINUS AlexPosn |
    TIMES AlexPosn |
    EQUALS AlexPosn |
    LESSTHAN AlexPosn |
    GREATERTHAN AlexPosn |
    NOT AlexPosn |
    AND AlexPosn |
    OR AlexPosn |
    XOR AlexPosn |
    IMPLIES AlexPosn |
    LPAREN AlexPosn |
    RPAREN AlexPosn |
    LET AlexPosn |
    ASSIGN AlexPosn |
    IN AlexPosn |
    END AlexPosn |
    IF AlexPosn |
    THEN AlexPosn |
    ELSE AlexPosn |
    FI AlexPosn |
    CONST AlexPosn String |
    ID AlexPosn String |
    EOF AlexPosn 
    deriving (Eq,Show)

token_posn (PLUS p) = p
token_posn (MINUS p) = p
token_posn (TIMES p) = p
token_posn (NEGATE p) = p
token_posn (EQUALS p) = p
token_posn (LESSTHAN p) = p
token_posn (GREATERTHAN p) = p
token_posn (NOT p) = p
token_posn (AND p) = p
token_posn (OR p) = p
token_posn (XOR p) = p
token_posn (IMPLIES p) = p
token_posn (LPAREN p) = p
token_posn (RPAREN p) = p
token_posn (LET p) = p
token_posn (ASSIGN p) = p
token_posn (IN p) = p
token_posn (END p) = p
token_posn (IF p) = p
token_posn (THEN p) = p
token_posn (ELSE p) = p
token_posn (FI p) = p
token_posn (CONST p _) = p
token_posn (ID p _) = p
token_posn (EOF p) = p




lineNum (AlexPn _ x _) = x
colNum (AlexPn _ _ y) = y

alexGetChar :: AlexInput -> Maybe Char
alexGetChar (_,_,_,[])   = Nothing
alexGetChar (_,_,_,c:cs) = Just c


scanTokens str = go (alexStartPos,'\n',[],str)
  where go inp@(pos,_,_,str) =
          case alexScan inp 0 of
                AlexEOF -> []
                AlexError char@((AlexPn _ line column),_,_,_) -> error $ " Unknown Token " ++ (show line) ++ ":" ++ (show column) ++ ":" ++ [fromJust (alexGetChar char)]
                AlexSkip  inp' len     -> go inp'
                AlexToken inp' len act -> act pos (take len str) : go inp'
}