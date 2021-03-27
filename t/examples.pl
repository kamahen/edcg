:- use_module('../prolog/edcg.pl'). % :- use_module(library(edcg)).
% Complete example exits in https://www2.eecs.berkeley.edu/Pubs/TechRpts/1990/CSD-90-583.pdf
%     (a copy is also in ../docs/CSD-90-583.pdf)

% Declare accumulators
edcg:acc_info(castor,_,_,_,true).
edcg:acc_info(fwd, T, In, Out, Out=[T|In]). % forward accumulator
edcg:acc_info(rev, T, Out, In, Out=[T|In]). % reverse accumulator
edcg:acc_info(adder, I, In, Out, plus(I,In,Out)). % adder

edcg:acc_info(code, T, Out, In, Out=[T|In]).
edcg:acc_info(size, T, In, Out, Out is In+T).

% Declare passed arguments
edcg:pass_info(pollux).

% Declare predicates using these hidden arguments
edcg:pred_info(p,1,[castor,pollux]).
edcg:pred_info(q,1,[castor,pollux]).
edcg:pred_info(r,1,[castor,pollux]).
edcg:pred_info(flist,1,[fwd]).
edcg:pred_info(flist_ssu,1,[fwd]).
edcg:pred_info(rlist,1,[rev]).
edcg:pred_info(rlist_ssu,1,[rev]).
edcg:pred_info(sum_first_n,1,[adder]).
edcg:pred_info(sum_first_n_ssu,1,[adder]).
edcg:pred_info(sum,0,[adder,dcg]).
edcg:pred_info(expr_code,1,[size,code]).
edcg:pred_info(expr_code_ssu,1,[size,code]).


% flist(N,[],List) creates the list [1,2,...,N]
flist(0) -->>
    !,
    [].
flist(N) -->>
    N>0,
    [N]:fwd,
    N1 is N-1,
    flist(N1).

flist_ssu(0) ==>>
    [].
flist_ssu(N) ==>>
    N>0, % TODO: this should be a guard
    [N]:fwd,
    N1 is N-1,
    flist_ssu(N1).


% rlist(N,List,[]) creates the list [N,...,2,1]
rlist(0) -->>
    !,
    [].
rlist(N) -->>
    N>0,
    [N]:rev,
    N1 is N-1,
    rlist(N1).

rlist_ssu(0) ==>>
    [].
rlist_ssu(N) ==>>
    N>0, % TODO: this should be a guard
    [N]:rev,
    N1 is N-1,
    rlist_ssu(N1).


% sum(N,0,Sum) adds the numbers 1,2,...,N
sum_first_n(0) -->>
    !,
    [].
sum_first_n(N) -->>
    N>0,
    [N]:adder,
    N1 is N-1,
    sum_first_n(N1).

sum_first_n_ssu(0) ==>>
    [].
sum_first_n_ssu(N) ==>>
    N>0, % TODO: this should be a guard
    [N]:adder,
    N1 is N-1,
    sum_first_n_ssu(N1).


sum(Xs,Sum) :-
    sum(0,Sum,Xs,[]).
sum -->>
    [X],
    !,
    [X]:adder,
    sum.
sum -->>
    [].


% Program that uses castor and pollux accumulators

p(X) -->>
    Y is X + 1,
    q(Y),
    r(Y).

q(Y) -->>
    C0/castor,
    castor/C,
    P/pollux,
    { format('q - Y: ~w, C0: ~q, C: ~q, P: ~q~n',[Y,C0,C,P]) },
    [ ]:castor. % Not needed.
r(Y) -->>
    C0/castor/C,
    P/pollux,
    { format('r - Y: ~w, C0: ~q, C: ~q, P: ~q~n',[Y,C0,C,P]) }.



% Program from the first paper with size, code accumulators.

expr_code(A+B) -->>
    expr_code(A),
    expr_code(B),
    [plus]:code,
    [1]:size.
expr_code(I) -->>
    {atomic(I)},
    [push(I)]:code,
    [1]:size.

expr_code_ssu(A+B) ==>>
    expr_code_ssu(A),
    expr_code_ssu(B),
    [plus]:code,
    [1]:size.
expr_code_ssu(I) ==>>
    {atomic(I)}, % TODO: this should be a guard
    [push(I)]:code,
    [1]:size.


:- use_module(library(plunit)).

:- begin_tests(edcg_examples).

test('flist solutions') :-
    flist(7,[],L),
    L == [1,2,3,4,5,6,7].

test('flist_ssu solutions') :-
    flist_ssu(7,[],L),
    L == [1,2,3,4,5,6,7].


test('rlist solutions') :-
    rlist(7,L,[]),
    L == [7,6,5,4,3,2,1].

test('rlist_ssu solutions') :-
    rlist_ssu(7,L,[]),
    L == [7,6,5,4,3,2,1].

test('sum_first_n: trivial') :-
    sum_first_n(0,0,Sum),
    Sum == 0.

test('sum_first_n_ssu: trivial') :-
    sum_first_n_ssu(0,0,Sum),
    Sum == 0.

test('sum_first_n: four') :-
    sum_first_n(4,0,Sum),
    Sum is 4+3+2+1.

test('sum_first_n_ssu: four') :-
    sum_first_n_ssu(4,0,Sum),
    Sum is 4+3+2+1.

test('sum [2,2,3]') :-
    sum([2,2,3],Sum),
    Sum is 2+2+3.

test(p1) :-
    with_output_to(string(Output), p(1,a,a,c)),
    assertion( Output == "q - Y: 2, C0: a, C: a, P: c\nr - Y: 2, C0: a, C: a, P: c\n" ).

test(p2) :-
    with_output_to(string(Output), p(1,a,C2,c)),
    assertion( C2 == a ),
    assertion( Output == "q - Y: 2, C0: a, C: a, P: c\nr - Y: 2, C0: a, C: a, P: c\n" ).

% The following example is modified from logtalk's port:
test(gemini_1) :-
    with_output_to(string(Output), p(10, S0, S, pollux)),
    with_output_to(string(S0_str), write(S0)),
    format(string(Expected),
           "q - Y: 11, C0: ~s, C: ~s, P: pollux~nr - Y: 11, C0: ~s, C: ~s, P: pollux~n",
           [S0_str, S0_str, S0_str, S0_str]),
    assertion( Output == Expected ),
    assertion( S0 == S ).

test(expr1, [nondet]) :-
    expr_code((a+b)+(c+d), 0, Size, Code, []),
    assertion(Size == 7),
    assertion(Code == [push(a), push(b), plus, push(c), push(d), plus, plus]).

test(expr1_ssu, [nondet]) :-
    expr_code_ssu((a+b)+(c+d), 0, Size, Code, []),
    assertion(Size == 7),
    assertion(Code == [push(a), push(b), plus, push(c), push(d), plus, plus]).

edcg:pred_info(p, 2, [dcg]). % For test ssu1

test(ssu1,
     [Expansion =@=
     (   p(b, X, S0, S) =>
             S0=S,
             X=2
     )]) :-
    expand_term((p(b, X) ==>> {X=2}), Expansion).

edcg:pred_info(p2, 2, [dcg]). % FOr test ssu_guard

test(ssu2_guard,
     [Expansion =@=
     (   p2(A, X, S0, S), A=a =>
             S0=S,
             X=1
     )]) :-
    expand_term((p2(A, X), ? A=a ==>> {X=1}), Expansion).


:- end_tests(edcg_examples).

end_of_file.
