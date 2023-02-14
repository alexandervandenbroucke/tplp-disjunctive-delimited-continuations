%%-----------------------------------------------------------------------------
%% Meta-interpreter for disjunctive delimited control.
%%
%% The meta-interpreter supports most basic Prolog features, except if then
%% else.
%%
%% Author: Alexander Vandenbroucke (alexander.vandenbroucke@sc.com)
%% Author: Tom Schrijvers          (tom.schrijvers@kuleuven.be)
%%

%%-----------------------------------------------------------------------------
%% Top-level predicate to find all solutions, non-deterministically.
solutions(G0) :-
    copy_term(G0,G),
    copy_term(G,GC),
    empty_disj(EmptyDisj),
    do_reset((GC,true),G,GC,Result,EmptyDisj),
    analyze_solutions(G0,G,Result).

analyze_solutions(G0,G,success(PatternCopy,Branch)) :-
    ( G0 = G
    ; copy_term(PatternCopy,PC),
      empty_disj(EmptyDisj),
      do_reset((Branch,true),PC,PatternCopy,Result,EmptyDisj),
      analyze_solutions(G0,PC,Result)
    ).
analyze_solutions(_,_,shift(_,_,_,_)) :-
    write('solutions: unexpected shift/1.\n'),
    fail.
analyze_solutions(_,_,failure) :- fail.



%%-----------------------------------------------------------------------------
%% Meta Interpreter

%% do_reset(Conjuction,Pattern,PatternCopy,Result,Disjunction)
%%
%% * On success or shift, Pattern contains the current solution.
%%
%% * PatternCopy is a fresh copy of Pattern. Note: the contents of PatternCopy
%%   are not always sensible after do_reset/5, hence PatternCopy should not be
%%   inspected afterwards.
%%
%% * Result is one of:
%%    - success(BranchPattern,Branch): BranchPattern is a fresh copy of
%%      Pattern, Branch is a disjunctive continuation (see below). In this case
%%      PatternCopy and Pattern are unified, to carry out the current
%%      substitution.
%%    - shift(Term,Conjunction,BranchPattern,Branch):
%%      Term is the term that was shifted, Conjuction is the conjunctive
%%      continuation. BranchPattern is a fresh copy of Pattern, Branch is the
%%      disjunctive continuation. Pattern and PatternCopy are unified to carry
%%      out the current substitution.
%%    - failure: when the conjunction and the disjunction fail
%%
%% * Conjunction: the current conjunctive goal. The variables it contains
%%   should not occur in Pattern. Moreover, the final conjunct should always be
%%   true/0. The conjunction must NOT be empty.
%%
%% * Disjunction: a disjunction/2, that contains an apart copy of the pattern and the
%%   disjunctive goal, or a single fail/0 predicate.
do_reset(true,Pattern,PatternCopy,Result,Disj) :-
    !,
    disjunction(BranchPattern,Branch) := Disj,
    Pattern := PatternCopy,
    Result  := success(BranchPattern,Branch).

%% fail/0-pattern
do_reset((fail,_Conj),Pattern,_,Result,Disj) :-
    !,
    backtrack(Pattern,Result,Disj).

%% true/0-pattern
do_reset((true,Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    do_reset(Conj,Pattern,PatternCopy,Result,Disj).

%% conjunction pattern
do_reset(((G1,G2),Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    do_reset((G1,(G2,Conj)),Pattern,PatternCopy,Result,Disj).
%% disjunction pattern
do_reset(((G1;G2),Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    copy_term(disjunction(PatternCopy,(G2,Conj)),Branch),
    disjoin(Branch,Disj,NewDisj),
    do_reset((G1,Conj),Pattern,PatternCopy,Result,NewDisj).

%% shift/1-pattern
do_reset((shift(X),Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    Pattern := PatternCopy,
    Disj    := disjunction(BranchPattern,Branch),
    Result  := shift(X,Conj,BranchPattern,Branch).

%% (new) reset/3-pattern
do_reset((reset(P,G,R),Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    copy_term(P-G,PC-GC),
    empty_disj(D),
    do_reset((GC,true),Q,PC,S,D),
    type_to_any(R,RAny),type_to_any(S,SAny),
    do_reset((P = Q, (RAny = SAny, Conj)),Pattern,PatternCopy,Result,Disj).

%% unification pattern
do_reset((X = Y,Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    ( X = Y -> do_reset(Conj,Pattern,PatternCopy,Result,Disj)
    ; backtrack(Pattern,Result,Disj)).

%%term non-equivalence pattern
do_reset((X \== Y,Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    ( X \== Y -> do_reset(Conj,Pattern,PatternCopy,Result,Disj)
    ; backtrack(Pattern,Result,Disj)).

%% copy_term/2-pattern
do_reset((copy_term(X,Y),Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    ( copy_term(X,Y) -> do_reset(Conj,Pattern,PatternCopy,Result,Disj)
    ; backtrack(Pattern,Result,Disj)).

%% not/1-pattern
do_reset((not(G),Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    copy_term(G,GC),
    do_reset((GC,true),_,_,R,_),
    ( R = failure -> do_reset(Conj,Pattern,PatternCopy,Result,Disj)
    ; R = shift(X,Cont,BranchPattern,Branch) ->
        BranchPattern = PatternCopy,
	Result = shift(X,(((not(Cont;Branch),Conj),true)),_,fail)
    ; backtrack(Pattern,Result,Disj)).

%% cut/0-pattern
do_reset((!,Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    do_reset(Conj,Pattern,PatternCopy,Result,Disj).

%% findall/3-pattern
do_reset((findall(T,G,L),Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    ( findall(T,G,L) -> do_reset(Conj,Pattern,PatternCopy,Result,Disj)
    ; backtrack(Pattern,Result,Disj)).

%% length/2-pattern
do_reset((length(L,X),Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    ( length(L,X) -> do_reset(Conj,Pattern,PatternCopy,Result,Disj)
    ; backtrack(Pattern,Result,Disj)).

%% member/2-pattern
do_reset((member(X,L),Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    ( member(X,L) -> do_reset(Conj,Pattern,PatternCopy,Result,Disj)
    ; backtrack(Pattern,Result,Disj)).

%% is/2-pattern
do_reset((is(R,Exp),Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    ( R is Exp -> do_reset(Conj,Pattern,PatternCopy,Result,Disj)
    ; backtrack(Pattern,Result,Disj)).

%% (<)/2-pattern
do_reset((<(X,Y),Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    ( X < Y -> do_reset(Conj,Pattern,PatternCopy,Result,Disj)
    ; backtrack(Pattern,Result,Disj)).

%% (>=)/2-pattern
do_reset((>=(X,Y),Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    ( X >= Y -> do_reset(Conj,Pattern,PatternCopy,Result,Disj)
    ; backtrack(Pattern,Result,Disj)).

%% (@<)/2-pattern
do_reset((@<(X,Y),Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    ( X @< Y -> do_reset(Conj,Pattern,PatternCopy,Result,Disj)
    ; backtrack(Pattern,Result,Disj)).

%% (@>=)/2-pattern
do_reset((@>=(X,Y),Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    ( X @>= Y -> do_reset(Conj,Pattern,PatternCopy,Result,Disj)
    ; backtrack(Pattern,Result,Disj)).

%% write/1-pattern
do_reset((write(T),Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    write(T),
    do_reset(Conj,Pattern,PatternCopy,Result,Disj).

%% sort/2-pattern
do_reset((sort(LIn,LOut),Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    sort(LIn,LOut),
    do_reset(Conj,Pattern,PatternCopy,Result,Disj).

%% clause pattern.
do_reset((G,Conj),Pattern,PatternCopy,Result,Disj) :-
    !,
    findall(GC-Body,(clause(G,Body), GC = G),Clauses),
    ( Clauses := [] ->
        backtrack(Pattern,Result,Disj)
    ; disjoin_clauses(G,Clauses,ClausesDisj),
      do_reset((ClausesDisj,Conj),Pattern,PatternCopy,Result,Disj)
    ).

disjoin_clauses(_,[],fail).
% The next clause is not necessary, but makes things prettier when tracing.
disjoin_clauses(G,[GC-Clause],(G=GC,Clause)) :- !.
disjoin_clauses(G,[GC-Clause|Clauses], ((G=GC,Clause) ; Disj) ) :-
    disjoin_clauses(G,Clauses,Disj).

%% backtracking
backtrack(Pattern,Result,Disj) :-
    ( empty_disj(Disj) ->
         Result := failure
    ; Disj := disjunction(PatternCopy,G) ->
         empty_disj(EmptyDisj),
	 do_reset((G,true),Pattern,PatternCopy,Result,EmptyDisj)
         %% TODO: could be more efficient if we pattern match on G?
    ).


%%-----------------------------------------------------------------------------
%% Disjunctions
%%
%% Disjunctions are of the from disjunction(Pattern,Goal), where Goal may
%% contain a disjunction.

%% Disjunctions are neither commutative nor associative. However empty_disj/1
%% is still the unit for disjoin/3.

%% The empty disjunction.
empty_disj(disjunction(_,fail)).

%% Disjoin two disjunctions.
%%
%% This operation is not commutative
disjoin(disjunction(_,fail),Disjunction,Disjunction) :- !.
disjoin(Disjunction,disjunction(_,fail),Disjunction) :- !.
disjoin(disjunction(PC1,G1),disjunction(PC2,G2),Disjunction) :-
    PC1 := PC2,
    Disjunction := disjunction(PC1, (G1 ; G2)).
% NOTE: things could probably be made more efficient by not unifying PC1
% and PC2, and keeping the disjunctions explicit, s.t. no fresh copy of
% G2 needs to be made, but this is way simpler.
