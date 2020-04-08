:- use_module('../prolog/edcg.pl').  % :- use_module(library(edcg)).
:- use_module(library(rbtrees), [rb_insert/4]).

% Declare accumulators
edcg:acc_info(set, X, In, Out, rb_insert(In,X,seen,Out)).

% Declare predicates using these hidden arguments
edcg:pred_info(unique,0,[dcg,set]).


%% unique(+Xs:list, -Count:integer, -Unique:list)
unique(Xs,Unique) :-
    rb_empty(Empty),
    unique(Xs,[],Empty,Final),
    rb_keys(Final, Unique).

unique -->>
    [X],      % X present in the list
    [X]:set,  % and present in the set
    !,
    unique.   % same for the rest of the list
unique -->>
    [].


:- use_module(library(plunit)).

:- begin_tests(edcg_unique).

test(t1) :-
    unique([],[]).

test(t2) :-
    unique([a],[a]).

test(t3) :-
    unique([a,b,a],[a,b]).

:- end_tests(edcg_unique).

end_of_file.
