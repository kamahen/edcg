:- module( edcg, [
    op(1200, xfx, '-->>'),   % Similar to '-->'
    op(1200, xfx, '==>>'),   % Similar to '-->'
    op( 990,  fx, '?'),      % For guards with '==>>'
    edcg_import_sentinel/0
]).

% If running a version of SWI-Prolog older than 8.3.19, define the
% '=>' operator to prevent syntax errors in this module.  The '==>>'
% operator is still defined in the module export, even though it'll
% generate a runtime error if it's used.
:- if(\+ current_op(_, _, '=>')).
:- op(1200, xfx, '=>').
:- endif.

:- use_module(library(debug), [debug/3]).
:- use_module(library(lists), [member/2, selectchk/3]).
:- use_module(library(apply), [maplist/3, maplist/4, foldl/4]).

% These predicates define extra arguments and are defined in the
% modules that use the edcg module.
:- multifile
    acc_info/5,
    acc_info/7,
    pred_info/3,
    pass_info/1,
    pass_info/2.

:- multifile
    prolog_clause:make_varnames_hook/5,
    prolog_clause:unify_clause_hook/5.

% True if the module being read has opted-in to EDCG macro expansion.
wants_edcg_expansion :-
    prolog_load_context(module, Module),
    wants_edcg_expansion(Module).

wants_edcg_expansion(Module) :-
    Module \== edcg,  % don't expand macros in our own library
    predicate_property(Module:edcg_import_sentinel, imported_from(edcg)).

% dummy predicate exported to detect which modules want EDCG expansion
edcg_import_sentinel.


% term_expansion/4 is used to work around SWI-Prolog's attempts to
% match variable names when doing a listing (or interactive trace) and
% getting confused; this sometimes results in a strange error message
% for an unknown extended_pos(Pos,N).

% Returning a variable for _Layout2 means "I don't know".
% See https://swi-prolog.discourse.group/t/strange-warning-message-from-compile-or-listing/3774
user:term_expansion(Term, Layout0, Expansion, Layout) :-
    wants_edcg_expansion,
    edcg_expand_clause(Term, Expansion, Layout0, Layout).

% TODO:
% prolog_clause:unify_clause_hook(Read, Decompiled, Module, TermPos0, TermPos) :-
%     wants_edcg_expansion(Module),
%     edcg_expand_clause(Read, Decompiled, TermPos0, TermPos).

% TODO:
%   prolog_clause:make_varnames_hook(ReadClause, DecompiledClause, Offsets, Names, Term) :- ...

% TODO: support ((H,PB-->>B) [same as regular DCG]
edcg_expand_clause((H-->>B), Expansion, TermPos0, _) :-
    edcg_expand_clause_wrap((H-->>B), Expansion, TermPos0, _).
edcg_expand_clause((H,PB==>>B), Expansion, TermPos0, _) :-
    edcg_expand_clause_wrap((H,PB==>>B), Expansion, TermPos0, _).
edcg_expand_clause((H==>>B), Expansion, TermPos0, _) :-
    edcg_expand_clause_wrap((H==>>B), Expansion, TermPos0, _).

edcg_expand_clause_wrap(Term, Expansion, TermPos0, TermPos) :-
    % TODO: the first check should always succeed, so remove it
    (   valid_termpos(Term, TermPos0)  % for debugging
    ->  true
    ;   throw(error(invalid_termpos_read(Term,TermPos0), _))
    ),
    (   '_expand_clause'(Term, Expansion, TermPos0, TermPos)
    ->  true
    ;   throw(error('FAILED_expand_clause'(Term, Expansion, TermPos0, TermPos), _))
    ),
    % (   valid_termpos(Expansion, TermPos) % for debugging
    % ->  true
    % ;   throw(error(invalid_termpos_expansion(Expansion, TermPos), _))
    % ).
    true.

% :- det('_expand_clause'/4).
% Perform EDCG macro expansion
% TODO: support ((H,PB-->>B) [same as regular DCG]
'_expand_clause'((H-->>B), Expansion, TermPos0, TermPos) =>
    TermPos0 = term_position(From,To,ArrowFrom,ArrowTo,[H_pos,B_pos]),
    TermPos  = term_position(From,To,ArrowFrom,ArrowTo,[Hx_pos,Bx_pos]),
    Expansion = (TH:-TB),
    '_expand_head_body'(H, B, TH, TB, NewAcc, H_pos,B_pos, Hx_pos,Bx_pos),
    '_finish_acc'(NewAcc),
    !.
'_expand_clause'((H,PB==>>B), Expansion, _TermPos0, _TermPos) => % TODO: TermPos
    % '==>>'(',',(H,PB),B)
    Expansion = (TH,Guards=>TB2),
    '_expand_guard'(PB, Guards), % TODO: TermPos
    '_expand_head_body'(H, B, TH, TB, NewAcc, _H_pos,_B_pos, _Hx_pos,_Bx_pos),
    '_finish_acc_ssu'(NewAcc, TB, TB2),
    !.
% H==>>B is essentially the same as H-->>B except that it produces =>
% But it needs to come last because otherwise H,PB would not be detected
'_expand_clause'((H==>>B), Expansion, TermPos0, TermPos) =>
    TermPos0 = term_position(From,To,ArrowFrom,ArrowTo,[H_pos,B_pos]),
    TermPos  = term_position(From,To,ArrowFrom,ArrowTo,[Hx_pos,Bx_pos]),
    Expansion = (TH=>TB2),
    '_expand_head_body'(H, B, TH, TB, NewAcc, H_pos,B_pos, Hx_pos,Bx_pos),
    '_finish_acc_ssu'(NewAcc, TB, TB2),
    !.

:- det('_expand_guard'/2).
% TODO: Do we want to expand the guards?
%       For now, just verify that they all start with '?'
'_expand_guard'((?G0,G2), Expansion) =>
    Expansion = (G, GE2),
    '_expand_guard_curly'(G0, G),
    '_expand_guard'(G2, GE2).
'_expand_guard'(?G0, G) =>
    '_expand_guard_curly'(G0, G).
'_expand_guard'(G, _) =>
    throw(error(type_error(guard,G),_)).

:- det('_expand_guard_curly'/2).
'_expand_guard_curly'({G}, G) :- !.
'_expand_guard_curly'(G, G).


:- det('_expand_head_body'/9).
'_expand_head_body'(H, B, TH, TB, NewAcc, H_pos,_B_pos, Hx_pos,_Bx_pos) :-
    functor(H, Na, Ar),
    '_has_hidden'(H, HList), % TODO: can backtrack - should it?
    debug(edcg,'Expanding ~w',[H]),
    '_new_goal'(H, HList, HArity, TH, H_pos, Hx_pos),
    '_create_acc_pass'(HList, HArity, TH, Acc, Pass),
    '_expand_goal'(B, TB, Na/Ar, HList, Acc, NewAcc, Pass),
    !.

% Expand a goal:
'_expand_goal'((G1,G2), Expansion, NaAr, HList, Acc, NewAcc, Pass) =>
    Expansion = (TG1,TG2),
    '_expand_goal'(G1, TG1, NaAr, HList, Acc, MidAcc, Pass),
    '_expand_goal'(G2, TG2, NaAr, HList, MidAcc, NewAcc, Pass).
'_expand_goal'((G1->G2;G3), Expansion, NaAr, HList, Acc, NewAcc, Pass) =>
    Expansion = (TG1->TG2;TG3),
    '_expand_goal'(G1, TG1, NaAr, HList, Acc, MidAcc, Pass),
    '_expand_goal'(G2, MG2, NaAr, HList, MidAcc, Acc1, Pass),
    '_expand_goal'(G3, MG3, NaAr, HList, Acc, Acc2, Pass),
    '_merge_acc'(Acc, Acc1, MG2, TG2, Acc2, MG3, TG3, NewAcc).
'_expand_goal'((G1*->G2;G3), Expansion, NaAr, HList, Acc, NewAcc, Pass) =>
    Expansion = (TG1*->TG2;TG3),
    '_expand_goal'(G1, TG1, NaAr, HList, Acc, MidAcc, Pass),
    '_expand_goal'(G2, MG2, NaAr, HList, MidAcc, Acc1, Pass),
    '_expand_goal'(G3, MG3, NaAr, HList, Acc, Acc2, Pass),
    '_merge_acc'(Acc, Acc1, MG2, TG2, Acc2, MG3, TG3, NewAcc).
'_expand_goal'((G1;G2), Expansion, NaAr, HList, Acc, NewAcc, Pass) =>
    Expansion = (TG1;TG2),
    '_expand_goal'(G1, MG1, NaAr, HList, Acc, Acc1, Pass),
    '_expand_goal'(G2, MG2, NaAr, HList, Acc, Acc2, Pass),
    '_merge_acc'(Acc, Acc1, MG1, TG1, Acc2, MG2, TG2, NewAcc).
'_expand_goal'((G1->G2), Expansion, NaAr, HList, Acc, NewAcc, Pass) =>
    Expansion = (TG1->TG2),
    '_expand_goal'(G1, TG1, NaAr, HList, Acc, MidAcc, Pass),
    '_expand_goal'(G2, TG2, NaAr, HList, MidAcc, NewAcc, Pass).
'_expand_goal'((G1*->G2), Expansion, NaAr, HList, Acc, NewAcc, Pass) =>
    Expansion = (TG1*->TG2),
    '_expand_goal'(G1, TG1, NaAr, HList, Acc, MidAcc, Pass),
    '_expand_goal'(G2, TG2, NaAr, HList, MidAcc, NewAcc, Pass).
'_expand_goal'((\+G), Expansion, NaAr, HList, Acc, NewAcc, Pass) =>
    Expansion = (\+TG),
    NewAcc = Acc,
    '_expand_goal'(G, TG, NaAr, HList, Acc, _TempAcc, Pass).
'_expand_goal'({G}, Expansion, _, _, Acc, NewAcc, _) =>
    Expansion = G,
    NewAcc = Acc.
'_expand_goal'(insert(X,Y), Expansion, _, _, Acc, NewAcc, _) =>
    Expansion = (LeftA=X),
    '_replace_acc'(dcg, LeftA, RightA, Y, RightA, Acc, NewAcc), !.
'_expand_goal'(insert(X,Y):A, Expansion, _, _, Acc, NewAcc, _) =>
    Expansion = (LeftA=X),
    '_replace_acc'(A, LeftA, RightA, Y, RightA, Acc, NewAcc),
    debug(edcg,'Expanding accumulator goal: ~w',[insert(X,Y):A]),
    !.
% Force hidden arguments in L to be appended to G:
'_expand_goal'((G:A), TG, _, _HList, Acc, NewAcc, Pass),
    \+'_list'(G),
    '_has_hidden'(G, []) =>
    '_make_list'(A, AList),
    '_new_goal'(G, AList, GArity, TG, _, _),
    '_use_acc_pass'(AList, GArity, TG, Acc, NewAcc, Pass).
% Use G's regular hidden arguments & override defaults for those arguments
% not in the head:
'_expand_goal'((G:A), TG, _, _HList, Acc, NewAcc, Pass),
    \+'_list'(G),
    '_has_hidden'(G, GList), GList\==[] =>
    '_make_list'(A, L),
    '_new_goal'(G, GList, GArity, TG, _, _),
    '_replace_defaults'(GList, NGList, L),
    '_use_acc_pass'(NGList, GArity, TG, Acc, NewAcc, Pass).
'_expand_goal'((L:A), Joiner, NaAr, _, Acc, NewAcc, _),
    '_list'(L) =>
    '_joiner'(L, A, NaAr, Joiner, Acc, NewAcc).
'_expand_goal'(L, Joiner, NaAr, _, Acc, NewAcc, _),
    '_list'(L) =>
    '_joiner'(L, dcg, NaAr, Joiner, Acc, NewAcc).
'_expand_goal'((X/A), Expansion, _, _, Acc, NewAcc, _),
    atomic(A),
    member(acc(A,X,_), Acc) =>
    Expansion = true,
    NewAcc = Acc,
    debug(edcg,'Expanding accumulator goal: ~w',[X/A]),
    !.
'_expand_goal'((X/A), Expansion, _, _, Acc, NewAcc, Pass),
    atomic(A),
    member(pass(A,X), Pass) =>
    Expansion = true,
    NewAcc = Acc,
    debug(edcg,'Expanding passed argument goal: ~w',[X/A]),
    !.
'_expand_goal'((A/X), Expansion, _, _, Acc, NewAcc, _),
    atomic(A),
    member(acc(A,_,X), Acc) =>
    Expansion = true,
    NewAcc = Acc.
'_expand_goal'((X/A/Y), Expansion, _, _, Acc, NewAcc, _),
    member(acc(A,X,Y), Acc),
    var(X), var(Y), atomic(A) =>
    Expansion = true,
    NewAcc = Acc.
'_expand_goal'((X/Y), true, NaAr, _, Acc, NewAcc, _) =>
    NewAcc = Acc,
    print_message(warning,missing_hidden_parameter(NaAr,X/Y)).
% Defaulty cases:
'_expand_goal'(G, TG, _HList, _, Acc, NewAcc, Pass) =>
    '_has_hidden'(G, GList), !,
    '_new_goal'(G, GList, GArity, TG, _, _),
    '_use_acc_pass'(GList, GArity, TG, Acc, NewAcc, Pass).

% ==== The following was originally acc-pass.pl ====

% Operations on the Acc and Pass data structures:

:- det('_create_acc_pass'/5).
% Create the Acc and Pass data structures:
% Acc contains terms of the form acc(A,LeftA,RightA) where A is the name of an
% accumulator, and RightA and LeftA are the accumulating parameters.
% Pass contains terms of the form pass(A,Arg) where A is the name of a passed
% argument, and Arg is the argument.
'_create_acc_pass'([], _, _, Acc, Pass) =>
    Acc = [],
    Pass = [].
'_create_acc_pass'([A|AList], Index, TGoal, Acc2, Pass),
    '_is_acc'(A) =>
    Acc2 = [acc(A,LeftA,RightA)|Acc],
    Index1 is Index+1,
    arg(Index1, TGoal, LeftA),
    Index2 is Index+2,
    arg(Index2, TGoal, RightA),
    '_create_acc_pass'(AList, Index2, TGoal, Acc, Pass).
'_create_acc_pass'([A|AList], Index, TGoal, Acc, Pass2),
    '_is_pass'(A) =>
    Pass2 = [pass(A,Arg)|Pass],
    Index1 is Index+1,
    arg(Index1, TGoal, Arg),
    '_create_acc_pass'(AList, Index1, TGoal, Acc, Pass).
'_create_acc_pass'([A|_AList], _Index, _TGoal, _Acc, _Pass),
    \+'_is_acc'(A),
    \+'_is_pass'(A) =>
    print_message(error,not_a_hidden_param(A)).


:- det('_use_acc_pass'/6).
% Use the Acc and Pass data structures to create the arguments of a body goal:
% Add the hidden parameters named in GList to the goal.
'_use_acc_pass'([], _, _, Acc, NewAcc, _) =>
    NewAcc = Acc.
% 1a. The accumulator A is used in the head:
%     Note: the '_replace_acc' guard instantiates MidAcc
'_use_acc_pass'([A|GList], Index, TGoal, Acc, NewAcc, Pass),
    '_replace_acc'(A, LeftA, RightA, MidA, RightA, Acc, MidAcc) =>
    Index1 is Index+1,
    arg(Index1, TGoal, LeftA),
    Index2 is Index+2,
    arg(Index2, TGoal, MidA),
    '_use_acc_pass'(GList, Index2, TGoal, MidAcc, NewAcc, Pass).
% 1b. The accumulator A is not used in the head:
'_use_acc_pass'([A|GList], Index, TGoal, Acc, NewAcc, Pass),
    '_acc_info'(A, LStart, RStart) =>
    Index1 is Index+1,
    arg(Index1, TGoal, LStart),
    Index2 is Index+2,
    arg(Index2, TGoal, RStart),
    '_use_acc_pass'(GList, Index2, TGoal, Acc, NewAcc, Pass).
% 2a. The passed argument A is used in the head:
'_use_acc_pass'([A|GList], Index, TGoal, Acc, NewAcc, Pass),
    '_is_pass'(A),
    member(pass(A,Arg), Pass) =>
    Index1 is Index+1,
    arg(Index1, TGoal, Arg),
    '_use_acc_pass'(GList, Index1, TGoal, Acc, NewAcc, Pass).
% 2b. The passed argument A is not used in the head:
'_use_acc_pass'([A|GList], Index, TGoal, Acc, NewAcc, Pass),
    '_pass_info'(A, AStart) =>
    Index1 is Index+1,
    arg(Index1, TGoal, AStart),
    '_use_acc_pass'(GList, Index1, TGoal, Acc, NewAcc, Pass).
% 3. Defaulty case when A does not exist:
'_use_acc_pass'([A|_GList], _Index, _TGoal, Acc, Acc, _Pass) =>
    print_message(error,not_a_hidden_param(A)).

:- det('_finish_acc'/1).
% Finish the Acc data structure:
% Link its Left and Right accumulation variables together in pairs:
% TODO: does this work correctly in the presence of cuts? ("!") - see README
'_finish_acc'([]).
'_finish_acc'([acc(_,Link,Link)|Acc]) :- '_finish_acc'(Acc).

:- det('_finish_acc_ssu'/3).
'_finish_acc_ssu'([], TB, TB).
'_finish_acc_ssu'([acc(_,Link0,Link1)|Acc], TB0, TB) :-
    '_finish_acc_ssu'(Acc, (Link0=Link1,TB0), TB).

% Replace elements in the Acc data structure:
% Succeeds iff replacement is successful.
'_replace_acc'(A, L1, R1, L2, R2, Acc, NewAcc) :-
    member(acc(A,L1,R1), Acc), !,
    '_replace'(acc(A,_,_), acc(A,L2,R2), Acc, NewAcc).

:- det('_merge_acc'/8).
% Combine two accumulator lists ('or'ing their values)
'_merge_acc'([], [], G1, G1, [], G2, G2, []) :- !.
'_merge_acc'([acc(Acc,OL,R)|Accs], [acc(Acc,L1,R)|Accs1], G1, NG1,
         [acc(Acc,L2,R)|Accs2], G2, NG2, [acc(Acc,NL,R)|NewAccs]) :- !,
    ( ( OL == L1, OL \== L2 ) ->
      MG1 = (G1,L1=L2), MG2 = G2, NL = L2
        ; ( OL == L2, OL \== L1 ) ->
      MG2 = (G2,L2=L1), MG1 = G1, NL = L1
        ; MG1 = G1, MG2 = G2, L1 = L2, L2 = NL ),
    '_merge_acc'(Accs, Accs1, MG1, NG1, Accs2, MG2, NG2, NewAccs).

% ==== The following was originally generic-util.pl ====

% Generic utilities special-util.pl

:- det('_match'/4).
% Match arguments L, L+1, ..., H of the predicates P and Q:
'_match'(L, H, _, _) :- L>H, !.
'_match'(L, H, P, Q) :- L=<H, !,
    arg(L, P, A),
    arg(L, Q, A),
    L1 is L+1,
    '_match'(L1, H, P, Q).


'_list'(L) :- nonvar(L), L=[_|_], !.
'_list'(L) :- L==[], !.

:- det('_make_list'/2).
'_make_list'(A, [A]) :- \+'_list'(A), !.
'_make_list'(L,   L) :-   '_list'(L), !.

:- det('_replace'/4).
% replace(Elem, RepElem, List, RepList)
'_replace'(_, _, [], []) :- !.
'_replace'(A, B, [A|L], [B|R]) :- !,
    '_replace'(A, B, L, R).
'_replace'(A, B, [C|L], [C|R]) :-
    \+C=A, !,
    '_replace'(A, B, L, R).

% ==== The following was originally special-util.pl ====

% Specialized utilities:

% Given a goal Goal and a list of hidden parameters GList
% create a new goal TGoal with the correct number of arguments.
% Also return the arity of the original goal.
'_new_goal'(Goal, GList, GArity, TGoal, H_pos, Hx_pos) :-
    functor(Goal, Name, GArity),
    '_number_args'(GList, GArity, TArity),
    functor(TGoal, Name, TArity),
    '_match'(1, GArity, Goal, TGoal),
    term_pos_expand(H_pos, GList, Hx_pos).

% Add the number of arguments needed for the hidden parameters:
'_number_args'([], N, N).
'_number_args'([A|List], N, M) :-
    '_is_acc'(A), !,
    N2 is N+2,
    '_number_args'(List, N2, M).
'_number_args'([A|List], N, M) :-
    '_is_pass'(A), !,
    N1 is N+1,
    '_number_args'(List, N1, M).
'_number_args'([_|List], N, M) :- !,
    % error caught elsewhere
    '_number_args'(List, N, M).

% Give a list of G's hidden parameters:
'_has_hidden'(G, GList) :-
    functor(G, GName, GArity),
    (   pred_info(GName, GArity, GList)
    ->  true
    ;   GList = []
    ).

% Create a TermPos for a goal with expanded parameters
term_pos_expand(Pos, _, _Expand_pos), var(Pos) => true. % TODO: remove DO NOT SUBMIT
term_pos_expand(From-To, [], Expand_pos) =>
    Expand_pos = From-To.
term_pos_expand(From-To, GList, Expand_pos) =>
    Expand_pos = term_position(From,To,From,To,PosExtra),
    maplist(pos_extra(To,To), GList, PosExtra).
term_pos_expand(term_position(From,To,FFrom,FTo,ArgsPos), GList, Expand_pos) =>
    Expand_pos = term_position(From,To,FFrom,FTo,ArgsPosExtra),
    maplist(pos_extra(To,To), GList, PosExtra),
    append(ArgsPos, PosExtra, ArgsPosExtra).
term_pos_expand(brace_term_position(From,To,ArgsPos), GList, Expand_pos) =>
    Expand_pos = btrace_term_position(From,To,ArgsPosExtra),
    maplist(pos_extra(To,To), GList, PosExtra),
    append(ArgsPos, PosExtra, ArgsPosExtra).
% Other things, such as `string_position` and
% `parentheses_term_position, shouldn't appear.
% And list_position (for accumulators) is handled separately

% Map an existing From,To to From-To. The 3rd parameter is from Hlist
% and is only used for controlling the number of elements in the
% calling maplist.
pos_extra(From, To, _, From-To).

% Succeeds if A is an accumulator:
'_is_acc'(A), atomic(A) => '_acc_info'(A, _, _, _, _, _, _).
'_is_acc'(A), functor(A, N, 2) => '_acc_info'(N, _, _, _, _, _, _).

% Succeeds if A is a passed argument:
'_is_pass'(A), atomic(A) => '_pass_info'(A, _).
'_is_pass'(A), functor(A, N, 1) => '_pass_info'(N, _).

% Get initial values for the accumulator:
'_acc_info'(AccParams, LStart, RStart) :-
    functor(AccParams, Acc, 2),
    '_is_acc'(Acc), !,
    arg(1, AccParams, LStart),
    arg(2, AccParams, RStart).
'_acc_info'(Acc, LStart, RStart) :-
    '_acc_info'(Acc, _, _, _, _, LStart, RStart).

% Isolate the internal database from the user database:
'_acc_info'(Acc, Term, Left, Right, Joiner, LStart, RStart) :-
    acc_info(Acc, Term, Left, Right, Joiner, LStart, RStart).
'_acc_info'(Acc, Term, Left, Right, Joiner, _, _) :-
    acc_info(Acc, Term, Left, Right, Joiner).
'_acc_info'(dcg, Term, Left, Right, Left=[Term|Right], _, []).

% Get initial value for the passed argument:
% Also, isolate the internal database from the user database.
'_pass_info'(PassParam, PStart) :-
    functor(PassParam, Pass, 1),
    '_is_pass'(Pass), !,
    arg(1, PassParam, PStart).
'_pass_info'(Pass, PStart) :-
    pass_info(Pass, PStart).
'_pass_info'(Pass, _) :-
    pass_info(Pass).

% Calculate the joiner for an accumulator A:
'_joiner'([], _, _, true, Acc, Acc).
'_joiner'([Term|List], A, NaAr, (Joiner,LJoiner), Acc, NewAcc) :-
    '_replace_acc'(A, LeftA, RightA, MidA, RightA, Acc, MidAcc),
    '_acc_info'(A, Term, LeftA, MidA, Joiner, _, _), !,
    '_joiner'(List, A, NaAr, LJoiner, MidAcc, NewAcc).
% Defaulty case:
'_joiner'([_Term|List], A, NaAr, Joiner, Acc, NewAcc) :-
    print_message(warning, missing_accumulator(NaAr,A)),
    '_joiner'(List, A, NaAr, Joiner, Acc, NewAcc).

% Replace hidden parameters with ones containing initial values:
'_replace_defaults'([], [], _).
'_replace_defaults'([A|GList], [NA|NGList], AList) :-
    '_replace_default'(A, NA, AList),
    '_replace_defaults'(GList, NGList, AList).

'_replace_default'(A, NewA, AList) :-  % New initial values for accumulator.
    functor(NewA, A, 2),
    member(NewA, AList), !.
'_replace_default'(A, NewA, AList) :-  % New initial values for passed argument.
    functor(NewA, A, 1),
    member(NewA, AList), !.
'_replace_default'(A, NewA, _) :-      % Use default initial values.
    A=NewA.

% ==== The following was originally messages.pl ====

:- multifile prolog:message//1.

prolog:message(missing_accumulator(Predicate,Accumulator)) -->
    ['In ~w the accumulator ''~w'' does not exist'-[Predicate,Accumulator]].
prolog:message(missing_hidden_parameter(Predicate,Term)) -->
    ['In ~w the term ''~w'' uses a non-existent hidden parameter.'-[Predicate,Term]].
prolog:message(not_a_hidden_param(Name)) -->
    ['~w is not a hidden parameter'-[Name]].
% === The following are for debugging term_expansion/4

% :- det(valid_termpos/2). % DO NOT SUBMIT
%! valid_termpos(+Term, ?TermPos) is semidet.
% Checks that a Term has an appropriate TermPos.
% This should always succeed:
%    read_term(Term, [subterm_positions(TermPos)]),
%    valid_termpos(Term, TermPos)
% Note that this can create a TermPos. Each clause ends with
% a cut, to avoid unneeded backtracking.
valid_termpos(Term, TermPos) :-
    (   valid_termpos_(Term, TermPos)
    ->  true
    ;   fail % throw(error(invalid_termpos(Term,TermPos), _)) % DO NOT SUBMIT
    ).

valid_termpos_(Var,    _From-_To) :- var(Var).
valid_termpos_(Atom,   _From-_To) :- atom(Atom), !.
valid_termpos_(Number, _From-_To) :- number(Number), !.
valid_termpos_(String,  string_position(_From,_To)) :- string(String), !.
valid_termpos_([],     _From-_To) :- !.
valid_termpos_({Arg},   brace_term_position(_From,_To,ArgPos)) :-
    valid_termpos(Arg, ArgPos), !.
valid_termpos_([Hd|Tl], list_position(_From,_To, ElemsPos, TailPos)) :-
    (   TailPos == none
    ->  maplist(valid_termpos, [Hd|Tl], ElemsPos),
        list_tail([Hd|Tl], _, [])
    ;   list_tail([Hd|Tl], HdPart, Tail),
        % Tail \== [], % note: can be var
        maplist(valid_termpos, HdPart, ElemsPos),
        valid_termpos(Tail, TailPos)
    ), !.
valid_termpos_(Term, term_position(_From,_To, FFrom,FTo,SubPos)) :-
    compound_name_arguments(Term, Name, Arguments),
    valid_termpos(Name, FFrom-FTo),
    maplist(valid_termpos, Arguments, SubPos), !.
valid_termpos_(Dict, dict_position(_From,_To,TagFrom,TagTo,KeyValuePosList)) :-
    dict_pairs(Dict, Tag, Pairs),
    valid_termpos(Tag, TagFrom-TagTo),
    foldl(valid_termpos_dict, Pairs, KeyValuePosList, []), !.
% key_value_position(From, To, SepFrom, SepTo, Key, KeyPos, ValuePos) is handled
% in valid_termpos_dict.
valid_termpos_(Term, parentheses_term_position(_From,_To,ContentPos)) :-
    valid_termpos(Term, ContentPos), !.
% TODO: documentation for quasi_quotation_position is wrong (SyntaxTo,SyntaxFrom should be SYntaxTerm,SyntaxPos).
valid_termpos_(_Term, quasi_quotation_position(_From,_To,SyntaxTerm,SyntaxPos,_ContentPos)) :-
    valid_termpos(SyntaxTerm, SyntaxPos), !.

:- det(valid_termpos_dict/3).
valid_termpos_dict(Key-Value, KeyValuePosList0, KeyValuePosList1) :-
    selectchk(key_value_position(_From,_To,_SepFrom,_SepTo,Key,KeyPos,ValuePos),
              KeyValuePosList0, KeyValuePosList1),
    valid_termpos(Key, KeyPos),
    valid_termpos(Value, ValuePos).

:- det(list_tail/3).
list_tail([X|Xs], HdPart, Tail) =>
    HdPart = [X|HdPart2],
    list_tail(Xs, HdPart2, Tail).
list_tail(Tail0, HdPart, Tail) => HdPart = [], Tail0 = Tail.

end_of_file.
