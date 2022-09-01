:- use_module(library(clpfd)).
% Kinship Data-Set

person(arti).
person(babli).
person(bunty).
person(X) :- parent(_,X).

parent(arti,babli).
parent(arti,bunty).
parent(babli,chintra).
parent(babli,chintan).
parent(bunty,divya).
parent(bunty,divesh).
male(bunty).
male(chintan).
male(divesh).

% Problem 1

childless(X) :-
    person(X),aggregate_all(count,parent(X,_) ,0).

% Problem 2
father(X,Y) :- parent(X,Y),male(X).
mother(X,Y) :- parent(X,Y),\+male(X).


% Problem 3
% solve_hanoi(N,Left,Right,Centre) <=> procedure to solve tower of hanoi problem from Left peg to Right peg using Centre peg
solve_hanoi(N,Left,Right,Centre) :-
    N =:= 1 -> format("move the disk from the top of ~w to ~w ~n",[Left,Right]);
    M is N-1,
    solve_hanoi(M,Left,Centre,Right),
    solve_hanoi(1,Left,Right,_),
    solve_hanoi(M,Centre,Right,Left).

hanoi_solver(N) :- solve_hanoi(N,left,right,centre).

%Problem 4

crypta_solver([A,B,C,D,E,F,G,H,I]) :-
    [A,B,C,D,E,F,G,H,I] ins 1..9,
    A+B+C #= D+E+F,D+E+F #= G+H+I,A+D+G #= G+H+I,
    B+E+H #= A+D+G,C+F+I #= B+E+H,A+E+I #= C+F+I,
    C+E+G #= A+E+I,
    labeling([ff],[A,B,C,D,E,F,G,H,I]).
    % enumeration predicate labeling for actual searchs of solutions
    % ff - First fail. Label the leftmost variable with smallest domain next, in order to detect infeasibility early
    
    

% Problem 5



% N - size of the board , Qs is list of queens such that Qs[i] = 'row # of queen i'

generate_safe_queens(N,Qs) :-
    length(Qs,N),
    Qs ins 1..N,
    safe_queens(Qs).

% none of the queens in Qs attack each other <=> safe_queens(Qs)
safe_queens([]):-!.
safe_queens([Q|Qs]) :-
    non_attacking(Q,Qs,1),
    safe_queens(Qs).

% Q doesn't attack any of the queens in Qs where head(Qs) is C cols apart from Q <=> non_attacking(Q,Qs,C)
non_attacking(_,[],_):-!.
non_attacking(Q,[Q1|Qs],C):-
    Q #\= Q1,
    abs(Q-Q1) #\= C,
    C1 #= C + 1, 
    non_attacking(Q,Qs,C1).

% Note :If N >= 4 then N-Queens problem has a solution so generate_safe_queens(N,Qs) will always terminate for N>= 4

% Solution generator
queens_generate(N):-
    generate_safe_queens(N,Qs),
    labeling([ff],Qs), 
    write(Qs).
% Output is a list [column] indexed by rows i.e. [col1,...,colN] <=> [(1,col1),...,(N,colN)] 
% Use queens_generate(N) in prolog interpreter to generate solutions for all values of N
% No solution is generated for the case of N = 2 , N = 3 (N-Queens problem has no solution).
    
    
    

    

