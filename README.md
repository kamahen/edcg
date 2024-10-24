# Synopsis

```prolog
:- use_module(library(edcg)).

% Declare accumulators
edcg:acc_info(adder, X, In, Out, plus(X,In,Out)).

% Declare predicates using these hidden arguments
edcg:pred_info(len,0,[adder,dcg]).
edcg:pred_info(increment,0,[adder]).

increment -->>
    [1]:adder.  % add one to the accumulator


len(Xs,N) :-
    len(0,N,Xs,[]).

len -->>
    [_],  % 'dcg' accumulator has an element
    !,
    increment,  % increment the 'adder' accumulator
    len.
len -->>
    [].
```

## Single-sided unification enhancement

If you're using [SWI-Prolog](http://www.swi-prolog.org) 8.3.21 or
later, you can use `==>>`, which generates clauses with `=>` instead
of `:-`. More details are given later in this document.

This enhancement is experimental and subject to change.



# Introduction

DCG notation gives us a single, hidden accumulator.  Extended DCG notation (implemented by this library) lets predicates have arbitrarily many hidden accumulators. As demonstrated by the Synopsis above, those accumulators can be implemented with arbitrary goals (like plus/3).

Benefits of this library:

  * avoid tedium and errors from manually threading accumulators through your predicates
  * add or remove accumulators with a single declaration
  * change accumulator implementation with a single declaration (ex, switching from ordsets to rbtrees)

# Syntax

Extended DCG syntax is very similar to DCG notation.  An EDCG is created with clauses whose neck is the `-->>` operator.  The following syntax is supported inside an EDCG clause:

  * `{Goal}` - don't expand any hidden arguments of `Goal`
  * `Goal` - expand all hidden arguments of Goal that are also in the head. Those hidden arguments not in the head are given default values.
  * `Goal:L` - If `Goal` has no hidden arguments then force the expansion of all arguments in `L` in the order given. If `Goal` has hidden arguments then expand all of them, using the contents of `L` to override the expansion. `L` is either a term of the form `Acc`, `Acc(Left,Right)`, `Pass`, `Pass(Value)`, or a list of such terms. When present, the arguments `Left`, `Right`, and `Value` override the default values of arguments not in the head.
  * `List:Acc` - Accumulate a list of terms in the accumulator `Acc`
  * `List` - Accumulate a list of terms in the accumulator `dcg`
  * `X/Acc` - Unify `X` with the left term for the accumulator `Acc`
  * `Acc/X` - Unify `X` with the right term for the accumulator `Acc`
  * `X/Acc/Y` - Unify `X` with the left and `Y` with the right term for the accumulator `Acc`
  * `insert(X,Y):Acc` - Insert the arguments `X` and `Y` into the chain implementing the accumulator `Acc`. This is useful when the value of the accumulator changes radically because `X` and `Y` may be the arguments of an arbitrary relation
  * `insert(X,Y)` - Insert the arguments `X` and `Y` into the chain implementing the accumulator `dcg`. This inserts the difference list X-Y into the accumulated list

# Declarations

## Declaration of Predicates

Predicates are declared with facts of the following form:

```prolog
pred_info(Name, Arity, List)
```

The predicate `Name/Arity` has the hidden parameters given in `List`. The parameters are added in the order given by `List` and their names must be atoms.

## Declaration of Accumulators

Accumulators are declared with facts in one of two forms. The short form is:

```prolog
acc_info(Acc, Term, Left, Right, Joiner)
```

The long form is:

```
acc_info(Acc, Term, Left, Right, Joiner, LStart, RStart)
```

In most cases the short form gives sufficient information. It declares the accumulator `Acc`, which must be an atom, along with the accumulating function, `Joiner`, and its arguments `Term`, the term to be accumulated, and `Left` & `Right`, the variables used in chaining.

The long form of `acc_info` is useful in more complex programs. It contains two additional arguments, `LStart` and `RStart`, that are used to give default starting values for an accumulator occurring in a body goal that does not occur in the head. The starting values are given to the unused accumulator to ensure that it will execute correctly even though its value is not used. Care is needed to give correct values for `LStart` and `RStart`. For DCG-like list accumulation both may remain unbound.

Two conventions are used for the two variables used in chaining depending on which direction the accumulation is done. For forward accumulation, `Left` is the input and `Right` is the output. For reverse accumulation, `Right` is the input and `Left` is the output.

## Declaration of Passed Arguments

Passed arguments are conceptually the same as accumulators with `=/2` as the joiner function.  Passed arguments are declared as facts in one of two forms. The short form is:

```prolog
pass_info(Pass)
```

The long form is:

```prolog
pass_info(Pass, PStart)
```

In most cases the short form is sufficient. It declares a passed argument `Pass`, that must be an atom. The long form also contains the starting value `PStart` that is used to give a default value for a passed argument in a body goal that does not occur in the head. Most of the time this situation does not occur.

## Single-sided unification enhancement - guards

With `==>>`, you can also specifiy "guards" in the head.
To avoid confusion with "push back lists" for `-->`, each guard
must be prefixed by the operator `?`.
Here's a trivial example:
```prolog
p(A, X) -->> A=a, !, X=1.
```
can be written with guards as:
```prolog
p(A), ? A=a ==>> {X=1}.
```

Because guards currently are not expanded, there is no need to use the
`{...}` notation for guards; but you can use it if you want.  Note
that SWI-Prolog's use of curly braces for dicts means that you need to
put a space between `?` and `{`.

## Differences between `-->>` and `-->`

The standard definition of DCGs allows a "push-back list" or
"right-hand context" in the head of a DCG rule. These seem to be of
limited use, and primarily used for doing a "look-ahead". For some
discussion on this, see [this comment by Richard
O'Keefe](https://swi-prolog.iai.uni-bonn.narkive.com/cOnL0aGn/push-back-lists-on-dcg-rule-heads)
and the [DCG Primer](https://www.metalevel.at/prolog/dcg).

## Cuts

[This comment by Richard
O'Keefe](https://swi-prolog.iai.uni-bonn.narkive.com/cOnL0aGn/push-back-lists-on-dcg-rule-heads)
discusses cuts in DCGs and why the original implementation used a
`C/3` predicate for unifications. In essence, if you move a unification over a cut,
you end up with a non-steadfast predicate.

EDCGs short-cut this, so if you use cuts, you might not get a correct
translation. Here's an example:
```prolog
p(a), [X] --> !, [X,a], q(X).
```

This should be translated as
```prolog
p(a, S0, S) :- !,
    /* note that the cut is done *exactly* where it appears */
    S0 = [X,a|S1],
    q(X, S1, S2),
    S = [X|S2].
```

The current SWI-Prolog implementation translates it to the following,
which has an extra `=/2` in it:
```prolog
p(a, S0, S) :-
    !,
    C=S0,
    C=[X, a|S1],
    q(X, S1, S2),
    S=[X|S2].
```

# Installation

Using SWI-Prolog 7.1 or later:

    ?- pack_install(edcg).

This module uses [semantic versioning](http://semver.org/).

Source code available and pull requests accepted at
http://github.com/kamahen/edcg (which takes over from
http://github.com/mndrix/edcg).

@license mit

# Additional documentation

Peter Van Roy's page: [Declarative Programming with State](https://www.info.ucl.ac.be/~pvr/edcg.html)

Technical Report UCB/CSD-90-583 [Extended DCG Notation: A Tool for Applicative Programming in Prolog](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1990/5471.html) by Peter Van Roy:

  * PDF is [here](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1990/CSD-90-583.pdf)
  * and mirrored [here](https://github.com/kamahen/edcg/blob/master/docs/CSD-90-583.pdf).

A short [Wikipedia article](https://en.wikipedia.org/wiki/Definite_clause_grammar#Extensions) on DCGs and extensions.
