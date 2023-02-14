%%=============================================================================
%% A (partial) implementation of Tarau and Majumdar's Interoperating logic
%% engines (2009) with delimited control.
%%
%%
%% This code uses the SWI-Prolog type_check package to type check Prolog code.
%% Type annotations do not influence the run-time behaviour, and can be
%% commented out on systems that do not support type checking.
%%
%% Author: Alexander Vandenbroucke

:- ['meta.pl'].

%==============================================================================
% Top level

%% Main predicate. It runs a goal G that may contain calls to engine
%% predicates (new_engine/3, get/2).
engines(G) :-
    engines(G,[]).

new_engine(Pattern,Goal,Interactor) :-
    shift(new_engine(Pattern,Goal,Interactor)).

get(Interactor,Answer) :-
    shift(get(Interactor,Answer)).

return(X) :-
    shift(return(X)).

%% Variant of engines/1 that takes a list of engine states.
%%
%% Note: the type system does not support heterogenous lists, and therefore,
%% all engines must have the same result type. This can be worked around by
%% setting R = pred.
engines(G,EngineList) :-
    copy_term(G,GC),
    reset(GC,GC,R),
    engines_result(G,GC,EngineList,R).

engines_result(_,_,_,failure) :-
    fail.
engines_result(G,GC,EngineList,success(BC,B)) :-
    (G = GC ; G = BC, engines(B,EngineList)).
engines_result(G,GC,EngineList,S) :-
    % handle new_engine/3
    S = shift(new_engine(Pattern,Goal,Interactor),C,BC,B),
    length(EngineList,Interactor),
    copy_term(Pattern-Goal,PatternCopy-GoalCopy),
    NewEngineList = [Interactor-engine(PatternCopy,GoalCopy)|EngineList],
    G = GC,
    G = BC,
    engines((C;B),NewEngineList).
engines_result(G,GC,EngineList,S) :-
    % handle shift/2
    S = shift(get(Interactor,Answer),C,BC,B),
    member(Interactor-Engine,EngineList),
    run_engine(Engine,NewEngine,Answer),
    update(Interactor,NewEngine,EngineList,NewEngineList),
    G = GC,
    G = BC,
    engines((C;B),NewEngineList).

%% Update the list of engine states.
update(K,NewV,[K-_|T],[K-NewV|T]).
update(K,NewV,[OtherK-V|T],[OtherK-V|T2]) :-
    K \== OtherK,
    update(K,NewV,T,T2).

%==============================================================================
% Running engines

%% Run an engine, return an updated engine, and an answer.
run_engine(engine(Pattern,Goal),NewEngine,Answer) :-
    reset(Pattern,Goal,Result),
    run_engine_result(Pattern,NewEngine,Answer,Result).

run_engine_result(Pattern,NewEngine,Answer,failure) :-
    NewEngine = engine(Pattern,fail),
    Answer    = no.
run_engine_result(Pattern,NewEngine,Answer,success(BPattern,B)) :-
    NewEngine = engine(BPattern,B),
    Answer    = the(Pattern).
run_engine_result(Pattern,NewEngine,Answer,shift(return(X),C,BPattern,B)) :-
    BPattern  = Pattern,
    NewEngine = engine(Pattern,(C;B)),
    Answer    = the(X).
