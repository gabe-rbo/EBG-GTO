%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%   EBG for GTO.
%   This version unifies the variables of EBG for GTO.
%   Currently looses non-determinism. To not loose non-determinism just cut out the meta-interpretation of g and t 
%     predicates and replace it with call/1
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


ebg(Goal, GeneralizedGoal, (GeneralizedGoal :- Condition), G, T, Unifications, (GeneralizedGoal :- GTO)) :-
    prolog_current_choice(ChoicePoint),
    ebg(Goal, GeneralizedGoal, Condition, ChoicePoint, [], G, [], T, [], Unifications),
    gto(G, T, GTO).

ebg(A, Gen, Cond, G_In, G_Mid, T_In, T_Mid, U_In, U_Out) :-
    prolog_current_choice(ChoicePoint),
    ebg(A, Gen, Cond, ChoicePoint, G_In, G_Mid, T_In, T_Mid, U_In, U_Out).


ebg(true, true, true, _ChoicePoint, G, G, T, T, U, U) :- !.

ebg(!, !, true, ChoicePoint, G, G, T, T, U, U) :-
    prolog_cut_to(ChoicePoint).


ebg(Goal, GeneralizedGoal, GeneralizedGoal, _ChoicePoint, G, G_Out, T, T, U_In, U_Out) :-
    g(GeneralizedGoal), !,
    my_append(G, GeneralizedGoal, G_Out),
    mi(Goal, GeneralizedGoal, Correspondences, []),
    my_concat(U_In, Correspondences, U_Out).

ebg(Goal, GeneralizedGoal, GeneralizedGoal, _ChoicePoint, G, G, T, T_Out, U_In, U_Out) :-
    t(GeneralizedGoal), !,
    my_append(T, GeneralizedGoal, T_Out),
    mi(Goal, GeneralizedGoal, Correspondences, []),
    my_concat(U_In, Correspondences, U_Out).


ebg(Var is Expr, GeneralizedVar is _GeneralizedExpr, true, _ChoicePoint, G, G, T, T, U, U) :- !,
    call(Var is Expr),
    GeneralizedVar = Var.

ebg(Goal, GeneralizedGoal, GeneralizedGoal, _ChoicePoint, G, G, T, T, U, U) :-
    Goal \= (_, _), Goal \= (_; _), Goal \= (_ -> _),
    predicate_property(Goal, built_in), !,
    call(Goal).


ebg(Goal, GeneralizedGoal, Cond, _ChoicePoint, G_In, G_Out, T_In, T_Out, U_In, U_Out) :-
    Goal \= (_, _), Goal \= (_; _), Goal \= (_ -> _),
    prolog_current_choice(ChoicePoint),
    clause(GeneralizedGoal, GeneralizedBody),
    copy_term((GeneralizedGoal :- GeneralizedBody), (Goal :- Body)),
    ebg(Body, GeneralizedBody, Cond, ChoicePoint, G_In, G_Out, T_In, T_Out, U_In, U_Out).


ebg((A, B), (GenA, GenB), Cond, ChoicePoint, G_In, G_Out, T_In, T_Out, U_In, U_Out) :-
    ebg(A, GenA, CondA, ChoicePoint, G_In, G_Mid, T_In, T_Mid, U_In, U_Mid),
    ebg(B, GenB, CondB, ChoicePoint, G_Mid, G_Out, T_Mid, T_Out, U_Mid, U_Out),
    simplify((CondA, CondB), Cond).

ebg((A -> B), (GenA -> GenB), Cond, ChoicePoint, G_In, G_Out, T_In, T_Out, U_In, U_Out) :-
    ebg(A, GenA, CondA, G_In, G_Mid, T_In, T_Mid, U_In, U_Mid), !,
    ebg(B, GenB, CondB, ChoicePoint, G_Mid, G_Out, T_Mid, T_Out, U_Mid, U_Out),
    simplify((CondA -> CondB), Cond).

ebg((A -> B; _), (GenA -> GenB), Cond, ChoicePoint, G_In, G_Out, T_In, T_Out, U_In, U_Out) :-
    ebg(A, GenA, CondA, G_In, G_Mid, T_In, T_Mid, U_In, U_Mid), !,
    ebg(B, GenB, CondB, ChoicePoint, G_Mid, G_Out, T_Mid, T_Out, U_Mid, U_Out),
    simplify((CondA -> CondB), Cond).

ebg((_ -> _; C), GenC, CondC, ChoicePoint, G_In, G_Out, T_In, T_Out, U_In, U_Out) :- !,
    ebg(C, GenC, CondC, ChoicePoint, G_In, G_Out, T_In, T_Out, U_In, U_Out).

ebg((A; B), (GenA; GenB), Cond, ChoicePoint, G_In, G_Out, T_In, T_Out, U_In, U_Out) :-
    (   ebg(A, GenA, CondA, ChoicePoint, G_In, G_Out, T_In, T_Out, U_In, U_Out)
    ;   ebg(B, GenB, CondB, ChoicePoint, G_In, G_Out, T_In, T_Out, U_In, U_Out)
    ),
    simplify((CondA; CondB), Cond).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Meta-Interpreter (Not fully implemented because most predicates are only conjunctions)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

mi(Goal, GeneralizedGoal, Correspondences, Accumulator) :-
    prolog_current_choice(ChoicePoint),
    mi(Goal, GeneralizedGoal, Correspondences, Accumulator, ChoicePoint).

mi(true, true, Correspondences, Correspondences, _ChoicePoint) :- !.

mi(!, !, Correspondences, Correspondences, ChoicePoint) :- prolog_cut_to(ChoicePoint).

mi(Goal, GeneralizedGoal, Correspondences, AccumulatorC, _ChoicePoint) :-
    g(Goal), !,
    GeneralizedGoal =.. [_|GenGoalArgs],
    Goal =.. [_|GoalArgs],
    create_correspondences(GenGoalArgs, GoalArgs, Corresp),
    my_concat(AccumulatorC, Corresp, AccumulatorC1),
    prolog_current_choice(ChoicePoint),
    clause(GeneralizedGoal, GeneralizedBody),
    copy_term((GeneralizedGoal :- GeneralizedBody), (Goal :- Body)),
    mi(Body, GeneralizedBody, Correspondences, AccumulatorC1, ChoicePoint).

mi(Goal, GeneralizedGoal, Correspondences, AccumulatorC, _ChoicePoint) :-
    t(Goal), !,
    GeneralizedGoal =.. [_|GenGoalArgs],
    Goal =.. [_|GoalArgs],
    create_correspondences(GenGoalArgs, GoalArgs, Corresp),
    my_concat(AccumulatorC, Corresp, AccumulatorC1),
    prolog_current_choice(ChoicePoint),
    clause(GeneralizedGoal, GeneralizedBody),
    copy_term((GeneralizedGoal :- GeneralizedBody), (Goal :- Body)),
    mi(Body, GeneralizedBody, Correspondences, AccumulatorC1, ChoicePoint).


mi(Goal, _GeneralizedGoal, Correspondences, Correspondences, _ChoicePoint) :-
    Goal \= (_, _), Goal\= (_; _), Goal \= (_ -> _), Goal \= !,
    predicate_property(Goal, built_in), !, call(Goal).

mi(Goal, GeneralizedGoal, Correspondences, AccumulatorC, _ChoicePoint) :-
    Goal \= (_, _), Goal\= (_; _), Goal \= (_ -> _), Goal \= !,
    prolog_current_choice(ChoicePoint),
    clause(GeneralizedGoal, GeneralizedBody),
    copy_term((GeneralizedGoal :- GeneralizedBody), (Goal :- Body)),
    mi(Body, GeneralizedBody, Correspondences, AccumulatorC, ChoicePoint).

mi((A, B), (GenA, GenB), Correspondences, Accumulator, ChoicePoint) :-
    mi(A, GenA, CorrespondA, Accumulator, ChoicePoint),
    mi(B, GenB, Correspondences, CorrespondA, ChoicePoint).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Simplifier for EBG Conditions
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


simplify((true, CondB), CondB) :- !.
simplify((CondA, true), CondA) :- !.
simplify((CondA, CondB), (CondA, CondB)).

simplify((true -> CondB), CondB) :- !.
simplify((CondA -> true), CondA) :- !.
simplify((CondA -> CondB), (CondA -> CondB)).

simplify((CondA; _CondB), CondA) :- var(_CondB), !.
simplify((_CondA; CondB), CondB) :- var(_CondA), !.
simplify((CondA; CondB), (CondA; CondB)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Aux. Predicates
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

create_correspondences([X], [Y], [X/Y]).
create_correspondences([X|L1], [Y|L2], [X/Y|L3]) :-
    create_correspondences(L1, L2, L3).

gto(G, T, GTO) :-
    schedule_goals(G, T, [], Body, []),
    list_to_conjunction(Body, GTO).

schedule_goals([], T, _CurrentVars, Body, Accumulator) :- my_append(Accumulator, T, Body).

schedule_goals([G1|G], T, CurrentVars, Body, BodyAccumulator) :-
    G1 =.. [_|G1Attr],
    my_term_variables(G1Attr, G1Vars),
    my_concat(CurrentVars, G1Vars, AllVars),
    can_be_tested(AllVars, T, Testable, []),
    subtract_list(T, Testable, RemainingTests),
    my_concat(BodyAccumulator, [G1|Testable], BodyAccumulator1),
    schedule_goals(G, RemainingTests, AllVars, Body, BodyAccumulator1).

can_be_tested(_GeneratedVars, [], Testable, Testable).

can_be_tested(GeneratedVars, [T1|Ts], Testable, Accumulator) :-
    T1 =.. [_|T1Attr],
    my_term_variables(T1Attr, T1Vars),
    (   is_subset(T1Vars, GeneratedVars) -> my_append(Accumulator, T1, Accumulator1),
                                        can_be_tested(GeneratedVars, Ts, Testable, Accumulator1)
    ;   can_be_tested(GeneratedVars, Ts, Testable, Accumulator)).

my_term_variables([], []) :- !.
my_term_variables([G1|Gs], [G1|R]) :- var(G1), !, my_term_variables(Gs, R).
my_term_variables([_G1|Gs], R) :-
    my_term_variables(Gs, R).

list_to_conjunction([A, B], (A, B)) :- !.
list_to_conjunction([A|C], (A, TC)) :-
    list_to_conjunction(C, TC).


my_append(L, [], L) :- !.
my_append([], L, [L]) :- !.
my_append([H|T], L, [H|R]) :-
    my_append(T, L, R).

my_compare(_T, []) :- !, fail.
my_compare(T, [G1|_]) :-
    same_term(T, G1), !.
my_compare(T, [_|GVars]) :-
    my_compare(T, GVars).

my_concat([], L2, L2).
my_concat([X|L1], L2, [X|L3]) :-
    my_concat(L1, L2, L3).

is_subset([], _) :- true.
is_subset([E|R], Set) :-
    my_compare(E, Set),
    is_subset(R, Set).

subtract_list([], _, R) :-
    R = [].
subtract_list([E|T], D, R) :-
    (   my_compare(E, D)
    ->  subtract_list(T, D, R)
    ;   R = [E|R1],
        subtract_list(T, D, R1)
    ).
