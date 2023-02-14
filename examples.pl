%%=============================================================================
%% Several examples of disjunctive delimited control:
%%   * cut/0 (!/0)
%%   * my_once/1 (once/1)
%%   * my_findall/3 (findall/3)
%%   * run_state/3 (global state)
%%   * branch and bound
%%   * nearest neighbour search
%%
%% Author: Alexander Vandenbroucke


:- [meta].

%% Example Predicates

p(1).
p(2).
p(3).

r(1).
r(2).
s(7).
s(8).


%==============================================================================
% cut reimplemented with reset

cut :- shift(cut).

%% Scope delimits the effect of the cut (i.e., a cut within scope(Goal), only
%% cuts away alternatives within Goal).
scope(Goal) :-
  copy_term(Goal,Copy),
  reset(Copy,Copy,Result),
  scope_result(Result,Goal,Copy).

scope_result(failure,_,_) :- 
  fail.
scope_result(success(_DisjCopy,_DisjGoal),Goal,Copy) :-
  Goal = Copy.
scope_result(success(DisjCopy,DisjGoal),Goal,_Copy) :-
  DisjCopy = Goal,
  scope(DisjGoal).
scope_result(shift(cut,ConjGoal,_DisjCopy,_DisjGoal),Goal,Copy) :-
  Goal = Copy,
  scope(ConjGoal).

pc(X,Y) :- r(X), cut, s(Y).
pc(4,2).


% ?- toplevel(scope(p(X,Y))).
% X = 1,
% Y = 7 ;
% X = 1,
% Y = 8 ;

%==============================================================================
% one solution

my_once(G0) :-
    reset(G0,G0,Result),
    Result = success(_,_).


% ?- toplevel(my_once(p(X))).
% X = 1;
% false.

%==============================================================================
% findall/3 reimplemented with reset

my_findall(Pattern,Goal,List) :-
    reset(Pattern,Goal,Result),
    my_findall_result(Result,Pattern,List).
        
my_findall_result(failure,_,[]).
my_findall_result(success(PatternCopy,Branch),Pattern,[Pattern|List]) :-
    my_findall(PatternCopy,Branch,List).
my_findall_result(shift(Term,Cont,PatternCopy,Branch),Pattern,List) :-
    copy_term(Pattern,PatternCopy2),
    shift(Term),
    my_findall(PatternCopy2,
	       ( PatternCopy2 = Pattern,Cont
	       ; PatternCopy2 = PatternCopy,Branch),
	       List).

% ?- toplevel(my_findall(X,p(X),L)).
% X = 1,
% L = [1, 2, 3] ;
% false.

%==============================================================================
% global state
%
% Run the stateful computation with run_state/3, access the state with get/1,
% change the state with put/1.

% Get the current state.
get(X) :- shift(get(X)).

% Write a new state.
put(X) :- shift(put(X)).

% Runs a stateful goal Goal, given an initial state, and returns the final
% state.
run_state(Goal,InitState,FinalState) :-
    copy_term(Goal,Pattern),
    reset(Pattern,Goal,Result),
    state_handler(Goal,Pattern,Result,InitState,FinalState).

state_handler(Goal,Pattern,success(PatternCopy,Branch),SIn,SOut) :-
    ( Goal = Pattern, SIn = SOut
    ; reset(PatternCopy,Branch,Result),
      state_handler(Goal,PatternCopy,Result,SIn,SOut)
    ).

state_handler(Goal,Pattern,shift(put(X),Cont,PatternCopy,Branch),_SIn,SOut) :-
    SMid = X,
    PatternCopy = Pattern,
    reset(Pattern,(Cont ; Branch),NewResult),
    state_handler(Goal,Pattern,NewResult,SMid,SOut).

state_handler(Goal,Pattern,shift(get(X),Cont,PatternCopy,Branch),SIn,SOut) :-
    X = SIn,
    PatternCopy = Pattern,
    reset(Pattern,(Cont ; Branch),NewResult),
    state_handler(Goal,Pattern,NewResult,SIn,SOut).
state_handler(_,_,failure,_,_,_) :- fail.

%% global state interacts with findall:
q(X) :- get(X).
q(X) :- get(Z), X is Z + 1.

example(L) :- my_findall(X,q(X),L), put(L).

%% ?- toplevel(run_state(example(L),0,X))
%% X = [0, 1] ;
%% false.

%==============================================================================
% print uncaught shifts
% This can be useful for debugging.

print_shift(G) :-
    reset(nil,G,R),
    handle_print_shift(R).

handle_print_shift(success(_,_)) :- !.
handle_print_shift(failure) :- !,fail.
handle_print_shift(R) :- write(R), write('\n').

%==============================================================================
% Branch & Bound

bound(V) :- shift(V).

run_nn((X0,Y0),BSP,(NX,NY)) :-
    toplevel(
	bb(
	    100-(100,100),
	    D-(X,Y),
	    nearest_neighbour((X0,Y0),BSP,D-(X,Y)),_-(NX,NY)
	)
    ).

bb(Value,Data,Goal,Min) :-
    reset(Data,Goal,Result),
    analyze_bb(Result,Value,Data,Min).

analyze_bb(success(BranchCopy,Branch),Value,Data,Min) :-
    write('success:'),
    write(Data),
    write('\n'),
    ( Data @< Value,
      bb(Data,BranchCopy,Branch,Min)
    ; Data @>= Value,
      bb(Value,BranchCopy,Branch,Min)
    ).

analyze_bb(shift(ShiftTerm,Cont,BranchCopy,Branch),Value,Data,Min) :-
    ( ShiftTerm @< Value, 
      bb(Value,Data,(Cont ; (BranchCopy = Data,Branch) ),Min)
    ; ShiftTerm @>= Value,
      write('branch with bound '), write(ShiftTerm), write(' pruned.\n'),
      bb(Value,BranchCopy,Branch,Min)
    ).

analyze_bb(failure,Value,_Data,Min) :- Value = Min.

%==============================================================================
% Nearest Neigbour Search
nearest_neighbour((X,Y),BSP,D-(NX,NY)) :-
    ( BSP = xsplit((SX,SY),Left,Right),
      DX is X - SX,
      branch((X,Y), (SX,SY), Left, Right, DX, D-(NX,NY))
    ; BSP = ysplit((SX,SY), Up, Down),
      DY is Y - SY,
      branch((X,Y), (SX,SY), Up, Down, DY, D-(NX,NY))
    ).

branch((X,Y), (SX,SY), BSP1, BSP2, D, Dist-(NX,NY)) :-
    BoundaryDistance is D*D,
    ( D < 0,
      TargetPart = BSP1, OtherPart = BSP2
    ; D >= 0,
      TargetPart = BSP2, OtherPart = BSP1
    ),
    ( nearest_neighbour((X,Y), TargetPart, Dist-(NX,NY))
    ; Dist is (X - SX) * (X - SX) + (Y - SY) * (Y - SY), % squared distance
      (NX,NY) = (SX,SY)
    ; bound(BoundaryDistance-nil),
      nearest_neighbour((X,Y), OtherPart,Dist-(NX,NY))
    ).


% Examples:

bsp1(BSP) :-
    BSP = xsplit((0,0), L, R),
    L   = ysplit((-0.2,0),empty,empty),
    R   = ysplit(( 0.2,0),empty,empty).

bsp2(BSP) :-
    BSP = xsplit((0,5),L,R),
    L = ysplit((-0.1,0),empty,empty),
    R = ysplit(( 0.1,0),empty,empty).

bsp3(BSP) :-
    BSP = xsplit((0,0),L,R),
    L   = ysplit((-0.1,0),empty,empty),
    R   = ysplit((   2,0),empty,empty).

bsp4(BSP) :-
    BSP = xsplit((0,10),L,R),
    L   = ysplit((-0.1,0),empty,empty),
    R   = ysplit((4   ,0),empty,empty).
    
% ?- bsp1(BSP), run_nn((1,0.1),BSP,(NX,NY)).
% success:0.6500000000000001-(0.2,0)
% success:1.01-(0,0)
% branch with bound 1-nil pruned.
% BSP=...,
% NX = 0.2,
% NY = 0 ;
% false.

% ?- bsp2(BSP), run_nn((1,0.1),BSP,(NX,NY)).
% success:0.8200000000000001-(0.1,0)
% success:25.010000000000005-(0,5)
% branch with bound 1-nil pruned.
% BSP = ...,
% NX = 0.1,
% NY = 0 ;
% false.

% Here, the final branch (-0.1,0) is not pruned, because it is not larger than
% the distance to (0,0).
% ?- bsp3(BSP), run_nn((1,0.1),BSP,(NX,NY)).
% success:1.01-(2,0)
% success:1.01-(0,0)
% success:1.2200000000000002-(-0.1,0)
% BSP = ...,
% NX = NY, NY = 0 ;
% false.

% Pruning does not happen in this case, but (0,10) is not reported.
% ?- bsp4(BSP), run_nn((1,0.1),BSP,(NX,NY)).
% success:9.01-(4,0)
% success:99.01-(0,10)
% success:1.2200000000000002-(-0.1,0)
% BSP = xsplit((0, 10), ysplit((-0.1, 0), empty, empty), ysplit((4, 0), empty, empty)),
% NX = -0.1,
% NY = 0 ;
% false.
    
