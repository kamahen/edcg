% -*- mode: Prolog -*-

% A simple puzzle solver, showing the use of EDCG notation.
% Solves https://en.wikipedia.org/wiki/Fox,_goose_and_bag_of_beans_puzzle

:- use_module('../prolog/edcg.pl').  % :- use_module(library(edcg)).
:- use_module(library(apply)).
:- use_module(library(lists)).

%! print_solution is semidet.
% Find all the solutions and print them out.
print_solution :-
    setof(Moves, puzzle_moves(Moves), Solutions),
    print_term(Solutions, []).

% The "move" accumulator is a standard DCG-like accumulator
edcg:acc_info(move, T, Out, In, Out=[T|In]).

% The "state" accumulator keeps a list of seen states in reverse order
% and when a new state is added, checks that the state hasn't already
% been seen.
edcg:acc_info(state, NewState, States0, States, add_state(NewState, States0, States)).

add_state(NewState, SeenStates, [NewState|SeenStates]) :-
    \+ memberchk(NewState, SeenStates).

% The "final_state" accumulator is an example of passing a "context".
edcg:pass_info(final_state).

% The puzzle//2 predicate takes 2 parameters (Side, State) and
% implicitly passes around 3 accumulators, for a total of 5 extra
% parameters (1 for final_state, 2 for move, 2 for state).
edcg:pred_info(puzzle, 2, [final_state, move, state]).

%! puzzle_moves(-Moves) is nondet.
% Find one solution, putting the moves into the Moves parameter.
puzzle_moves(Moves) :-
    puzzle(hither,  % initial side
           state{farmer:hither, fox:hither, goose:hither, beans:hither},  % initial state
           state{farmer:yon,    fox:yon,    goose:yon,    beans:yon},     % final state
           Moves, [],  % move accumulator
           [], _       % seen_states accumulator
          ).

%! puzzle(+Side, +State) is nondet.
%         accumulators: [final_state, move, state]
% Given the current Side (hither, yon) and a State, compute a new
% move; terminate if already at the final state.
puzzle(_Side, State) -->>
    State/final_state,  % FinalState/final_state, FinalState = State
    !.
puzzle(Side, State) -->>
    % The "{...}" isn't needed because there are no edcg:pred_info/3
    % clauses for these predicates, but it's good documentation.
    { other_side(Side, OtherSide),
      cross_in_boat(State, Passengers),
      new_state([farmer|Passengers], OtherSide, State, State2),
      valid_state(State2),
      select(farmer, Passengers, PassengersWithoutFarmer)
    },
    [ State2 ]:state,
    [ PassengersWithoutFarmer:Side->OtherSide:State2 ]:move,
    puzzle(OtherSide, State2).

%! cross_in_boat(+State, -Passengers:list) is nondet.
% Select a passenger (or none) from the State; Passengers is either
% the farmer or farmer plus a single passenger.
cross_in_boat(_State, [farmer]).
cross_in_boat(State, [farmer, Passenger]) :-
    get_dict(Passenger, State, State.farmer), % Select passenger from same location as farmer
    Passenger \= farmer.

:- det(new_state/4).
%! new_state(+Passengers, +OtherSide, +State, -State2) is det.
% Generate a new State2 with the Passengers (which will also include
% the farmer) on the OtherSide.
new_state(Passengers, OtherSide, State, State2) :-
    foldl(state_move_passenger(OtherSide), Passengers, State, State2).

:- det(state_move_passenger/4).
%! state_move_passenger(+OtherSide, +Passenger, +State, -State2)  is det.
% Create a new state with the Passenger on the OtherSide.
state_move_passenger(OtherSide, Passenger, State, State2) :-
    put_dict(Passenger, State, OtherSide, State2).

%! valid_state(+State) is semidet.
% Test whether a State is valid (fox can't eat goose, goose can't eat beans)
valid_state(state{farmer:FarmerSide, fox:FoxSide, goose:GooseSide, beans:BeansSide}) :-
    (FoxSide \= GooseSide; FoxSide = FarmerSide),
    (GooseSide \= BeansSide; GooseSide = FarmerSide).

%! other_side(+Side, -OtherSide) is det.
% Enumerate the hither/yon, yon/hither values for switching sides.
other_side(hither, yon).
other_side(yon,    hither).

