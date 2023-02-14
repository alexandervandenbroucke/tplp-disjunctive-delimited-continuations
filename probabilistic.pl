%%=============================================================================
%% Simulation of the PRISM and ProbLog using disjunctive delimited control.
%% Computed probabilities are only correct for definite, non-looping programs.
%%
%% To run a PRISM goal, use toplevel(prob(Goal)).
%% To run a ProbLog goal, use toplevel(prob(problog(Goal))).
%% 
%% Author: Alexander Vandenbroucke

:- ['meta.pl'].
:- discontiguous values_x/3.

%==============================================================================
% PRISM interpreter

% Probabilistically select a value for a switch Key.
msw(Key,Value) :-
    shift(msw(Key,Value)).

% Run a PRISM goal.
prob(Goal) :-
    prob(Goal,ProbOut),
    write(Goal), write(': '), write(ProbOut), write('\n').

prob(Goal,ProbOut) :-
    copy_term(Goal,GoalCopy),
    reset(GoalCopy,GoalCopy,Result),
    analyze_prob(GoalCopy,Result,ProbOut).

analyze_prob(_,failure,0.0).
analyze_prob(_,success(_,_),1.0).

analyze_prob(_,shift(msw(K,V),C,_,Branch),ProbOut) :-
    values_x(K,Values,Probabilities),
    msw_prob(V,C,Values,Probabilities,0.0,ProbOfMsw),
    prob(Branch,BranchProb),
    ProbOut is ProbOfMsw + BranchProb.

msw_prob(_,_,[],[],Acc,Acc).
msw_prob(V,C,[Value|Values],[Prob|Probs],Acc,ProbOfMsw) :-
    prob((V = Value,C),ProbOut),
    NewAcc = Prob*ProbOut + Acc,
    msw_prob(V,C,Values,Probs,NewAcc,ProbOfMsw).

prism(Goal) :-
     prob(Goal,ProbOut),
     write(Goal), write(': '), write(ProbOut), write('\n').

%% Example:

values_x(f,[t,f],[0.5,0.5]).

% ?- toplevel(prob((msw(i,t),msw(i,t)))).
% (msw(f,t), msw(f,t))): 0.25

values_x(coin,[h,t],[0.5,0.5]).

twoHeads :- msw(coin,h),msw(coin,h).
oneHead :- msw(coin,V),(V = h ; V = t, msw(coin,h)).
oneHeadWrong :- msw(coin,h) ; msw(coin,h).


%==============================================================================
%% ProbLog interpreter

% Signal a fact.
fact(F) :-
    shift(fact(F,V)),
    V = t.

is_true(F,Pc) :- member(F-t,Pc).
is_false(F,Pc) :- member(F-f,Pc).

problog(Goal) :- problog(Goal,[]).
problog(Goal,Pc) :-
    reset(Goal,Goal,Result),
    analyze_problog(Result,Pc).

analyze_problog(success(_,_),_Pc).
analyze_problog(shift(fact(F,V),C,_,Branch),Pc) :-
    is_true(F,Pc),
    V = t,
    problog((C;Branch),Pc).
analyze_problog(shift(fact(F,V),C,_,Branch),Pc) :-
    is_false(F,Pc),
    V = f,
    problog((C;Branch),Pc).
analyze_problog(shift(fact(F,V),C,_,Branch),Pc) :-
    not(is_true(F,Pc)),
    not(is_false(F,Pc)),
    msw(F,V),
    problog((C;Branch),[F-V|Pc]).
analyze_problog(failure,_Pc) :- fail.

%% Example:

values_x(f1(_),[t,f],[0.5,0.5]).
f1(X) :- fact(f1(X)).

p :- f1(1).
p :- f1(2).

q(_) :- f1(1),not(f1(2)).

% ?- toplevel(prob(problog((f1(X),f1(X)))))
% problog((f1(X),f1(X))): 0.5


values_x(coin1,[t,f],[0.5,0.5]).
values_x(coin2,[t,f],[0.5,0.5]).
coin1 :- fact(coin1).
coin2 :- fact(coin2).

oneHeadP :- coin1 ; coin2.

% ?- toplevel(prob(problog(oneHeadP)))
% problog(oneHeadP): 0.75
