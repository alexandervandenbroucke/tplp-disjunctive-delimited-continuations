%%=============================================================================
%% A (partial) implementation of Tarau and Majumdar's Interoperating logic
%% engines (2009) with delimited control.
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

to_engine(Interactor,Data) :-
    shift(to_engine(Interactor,Data)).

return(X) :-
    shift(return(X)).

from_engine(Data) :-
    shift(from_engine(Data)).

%% Variant of engines/1 that takes a list of engine states.
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
    mk_engine(PatternCopy,GoalCopy,Engine),
    NewEngineList = [Interactor-Engine|EngineList],
    G = GC,
    G = BC,
    engines((C;B),NewEngineList).
engines_result(G,GC,EngineList,S) :-
    % handle get/2
    S = shift(get(Interactor,Answer),C,BC,B),
    member(Interactor-Engine,EngineList),
    run_engine(Engine,EngineOut,Answer),
    update(Interactor,EngineOut,EngineList,NewEngineList),
    G = GC,
    G = BC,
    engines((C;B),NewEngineList).
engines_result(G,GC,EngineList,S) :-
    % handle to_engine/2
    S = shift(to_engine(Interactor,Data),C,BC,B),
    member(Interactor-Engine,EngineList),
    copy_term(Data,Message),
    queue(Message,Engine,EngineOut),
    update(Interactor,EngineOut,EngineList,NewEngineList),
    G = GC,
    G = BC,
    engines((C;B),NewEngineList).

%% Update the list of engine states.
update(K,NewV,[K-_|T],[K-NewV|T]).
update(K,NewV,[OtherK-V|T],[OtherK-V|T2]) :-
    K \== OtherK,
    update(K,NewV,T,T2).

%% Create a new engine
mk_engine(Pattern,Goal,Engine) :- Engine = engine(Pattern,Goal,[]).

%% Queue a message on an engine
queue(Message,Engine,EngineOut) :-
    Engine = engine(Pattern,Goal,Messages),
    append(Messages,[Message],NewMessages),
    EngineOut = engine(Pattern,Goal,NewMessages).



%==============================================================================
% Running engines

%% Run an engine, return an updated engine, and an answer.
run_engine(engine(Pattern,Goal,Messages),EngineOut,Answer) :-
    reset(Pattern,Goal,Result),
    run_engine_result(Pattern,Messages,EngineOut,Answer,Result).

run_engine_result(Pattern,Messages,EngineOut,Answer,failure) :-
    EngineOut = engine(Pattern,fail,Messages),
    Answer    = no.
run_engine_result(Pattern,Messages,EngineOut,Answer,success(BPattern,B)) :-
    EngineOut = engine(BPattern,B,Messages),
    Answer    = the(Pattern).
run_engine_result(Pattern,Messages,EngineOut,Answer,Shift) :-
    Shift     = shift(return(X),C,BPattern,B),
    BPattern  = Pattern,
    EngineOut = engine(Pattern,(C;B),Messages),
    Answer    = the(X).
run_engine_result(Pattern,Messages,EngineOut,Answer,Shift) :-
    Shift     = shift(from_engine(Data),C,BPattern,B),
    BPattern  = Pattern,
    Continue  = engine(Pattern,G,NewMessages),
    ( % message queue is empty, from_engine/2 fails
      Messages = [], NewMessages = Messages, G = B 
    ; % dequeue the next message
      Messages = [Data|NewMessages], G = (C;B)
    ),
    run_engine(Continue,EngineOut,Answer).

%==============================================================================
% Examples

ask_engine(Engine,Query,Result) :-
    to_engine(Engine,Query),
    get(Engine,Result).

engine_yield(Answer) :-
    from_engine(Answer :- Goal),
    call(Goal),return(Answer).

echo :-
    from_engine(Message),
    writeln('Ping' : Message),
    return(Message).

ping(Ping) :-
    new_engine(_,echo,E),
    to_engine(E,Ping),
    get(E,the(Pong)),
    writeln('Pong' : Pong),
    Ping = Pong.

% ?- toplevel(engines(ping(msg))).
% Ping:msg
% Pong:msg
% true ;
% false.

% A small example due to Tarreau and Majmudar
sum_loop(S1) :- engine_yield(S1-->S2), sum_loop(S2).

inc_test(R1,R2) :-
    new_engine(_,sum_loop(0),E),
    ask_engine(E,((S1 --> S2) :- S2 is S1 + 2),R1),
    ask_engine(E,((S1 --> S2) :- S2 is S1 + 5),R2).

% ?- toplevel(engines(inc_test(R1,R2))).
% R1 = the((0-->2)),
% R2 = the((2-->7)) ;
% false.
