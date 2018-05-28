%lookup
lookup([], variable(_), _) :- !,fail.
lookup([(variable(X),T)| _], variable(X), T) :- !.
lookup([(variable(X),_)| _], variable(X), _) :- !, fail.
lookup([(variable(_),_)| Xs], variable(X), T) :- lookup(Xs, variable(X), T).

hasType(Gamma, variable(X), T) :- lookup(Gamma, variable(X), T),!.

hasType(_, const(E), intT) :- integer(E).
hasType(_,true,boolT).
hasType(_,false,boolT).

hasType(Gamma, constructor(A,B), T) :- string(A), hasType(Gamma, B, T1), T = type(A, T1).

head([], _) :- !,fail.
head([X|Xs], X).

hasType(Gamma, switch_case(N, L), T) :- hasType(Gamma, N, T1), member((default, E), L), hasType(Gamma, E, T2), hasT(Gamma, L, cartesianT(T1,T2)), T = switch_caseType,!.

hasT(Gamma, [], _):-!.
hasT(Gamma, [(default,X2)|Xs], cartesianT(T1, T2)) :- hasType(Gamma, X2, T2), hasT(Gamma, Xs, cartesianT(T1,T2)).
hasT(Gamma, [(X1,X2)|Xs], cartesianT(T1, T2)) :- hasType(Gamma, X1, T1), hasType(Gamma, X2, T2), hasT(Gamma, Xs, cartesianT(T1,T2)).

hasType(Gamma, absolute(E),intT) :- hasType(Gamma, E, intT),!.
hasType(Gamma, plus(E1,E2), intT) :- hasType(Gamma, E1, intT), hasType(Gamma, E2, intT),!.
hasType(Gamma, minus(E1,E2), intT) :- hasType(Gamma, E1, intT), hasType(Gamma, E2, intT),!.
hasType(Gamma, times(E1,E2), intT) :- hasType(Gamma, E1, intT), hasType(Gamma, E2, intT),!.
hasType(Gamma, div(E1,E2), intT) :- hasType(Gamma, E1, intT), hasType(Gamma, E2, intT),!.
hasType(Gamma, mod(E1,E2), intT) :- hasType(Gamma, E1, intT), hasType(Gamma, E2, intT),!.
hasType(Gamma, expo(E1,E2), intT) :- hasType(Gamma, E1, intT), hasType(Gamma, E2, intT),!.

hasType(Gamma,not(E1), boolT) :- hasType(Gamma, E1, boolT),!.
hasType(Gamma,and(E1,E2), boolT) :- hasType(Gamma, E1, boolT), hasType(Gamma, E2, boolT),!.
hasType(Gamma,or(E1,E2), boolT) :- hasType(Gamma, E1, boolT), hasType(Gamma, E2, boolT),!.
hasType(Gamma,implies(E1,E2), boolT) :- hasType(Gamma, E1, boolT), hasType(Gamma, E2, boolT),!.

hasType(Gamma, greaterThan(E1,E2), boolT) :- hasType(Gamma, E1, intT), hasType(Gamma, E2, intT),!.
hasType(Gamma, lessThan(E1,E2), boolT) :- hasType(Gamma, E1, intT), hasType(Gamma, E2, intT),!.
hasType(Gamma, greater(E1,E2), boolT) :- hasType(Gamma, E1, intT), hasType(Gamma, E2, intT),!.
hasType(Gamma, lesser(E1,E2), boolT) :- hasType(Gamma, E1, intT), hasType(Gamma, E2, intT),!.

hasType(Gamma, equal(E1,E2), boolT) :- hasType(Gamma, E1, T1), hasType(Gamma, E2, T1),!.

hasType(Gamma, if_then_else(E0,E1,E2), T) :- hasType(Gamma, E0, boolT), hasType(Gamma, E1, T), hasType(Gamma, E2, T),!.

hasType(Gamma, let_in_end(D, E), T) :- typeElaborate(Gamma, D, GammaPrime), append(GammaPrime, Gamma, GammaNew), hasType(GammaNew, E, T),!.

hasType(Gamma, abs(variable(X), E1), arrowT(T1, T2)) :- hasType([(variable(X), T1)| Gamma], E1, T2),!.

hasType(Gamma, pair(E1, E2), cartesianT(T1, T2)) :- hastype(Gamma, E1, T1), hasType(Gamma, E2, T2),!.

hasType(Gamma, functionCall(E1, E2), T2) :- hasType(Gamma, E1, arrowT(T1, T2)), hasType(Gamma, E2, T1),!.

hasType(_, tuple([]), cartesianT([])) :- !.
hasType(Gamma, tuple([X|Xs]), cartesianT([T|Ts])) :- hasType(Gamma, X, T), hasType(Gamma, tuple(Xs), cartesianT(Ts)),!.

hasType(Gamma, proj(I, tuple(L)), T) :- nth0(I, L, X), hasType(Gamma, X, T). 

%typeElaborate(Gamma, D, GammaPrime).
typeElaborate(Gamma, def(X,E), GammaPrime) :- hasType(Gamma, E, T), GammaPrime = [(X,T)].
typeElaborate(Gamma, D1;D2, GammaPrime) :- typeElaborate(Gamma, D1, Gamma1), append(Gamma1, Gamma, GammaNew), typeElaborate(GammaNew, D2, Gamma2), append(Gamma2,Gamma1,GammaPrime).
typeElaborate(Gamma, parallel(D1,D2), GammaPrime) :- noComVar(D1, D2), typeElaborate(Gamma, D1, Gamma1), typeElaborate(Gamma, D2, Gamma2), append(Gamma2,Gamma1,GammaPrime).
typeElaborate(Gamma, local_in(D1, D2), GammaPrime) :- typeElaborate(Gamma, D1, Gamma1), append(Gamma1, Gamma, Gamma2), typeElaborate(Gamma2, D2, GammaPrime).

dv(def(X,_), [X]).
dv(D1;D2, L) :- dv(D1, L1), dv(D2, L2), append(L1,L2, L).
dv(parallel(D1,D2), L) :- noComVar(D1, D2), dv(D1, L1), dv(D2, L2), append(L1,L2, L).
dv(local_in(_, D2), L) :- dv(D2, L).

noComVar(D1, D2) :- dv(D1, A), dv(D2, B), intersectNull(A,B).

intersectNull([], _):- !.
intersectNull(_, []):- !.
intersectNull([X|Xs], B):- \+ member(X, B), intersectNull(Xs, B).
