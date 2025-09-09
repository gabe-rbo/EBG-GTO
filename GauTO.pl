%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%   EBG for GTO (Explanation-Based Generalization for Generate-Test-Optimize).
%   In this version, we don't meta-interpret the generation and test clauses.
%   However, there is a one-to-one correspondence of variables from the head
%   recursive call to the tail recursive call.
%   This correspondence is precisely given by the fact that tail recursion is
%   destructive while head recursion is constructive. Due to this, in tail
%   recursion, the initial argument is not explicit, unlike head recursion,
%   where it together with the base case are used to build the solution.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


gauto(Goal, GenGoal, (GenGoal :- Condition), G, T, (GenGoal :- GTO)) :-
    prolog_current_choice(ChoicePoint),
    ebg(Goal, GenGoal, Condition, ChoicePoint, [], G, [], T),
    GenGoal =.. [_, InitArg, Solution], % We're assuming the clause head contains only 2 arguments
    (   \+ var(InitArg) -> invert_variables_in_list(InitArg, Solution, G, NewG), reverse(NewG, GInv), gto(GInv, T, GTO) % Head Recursion
    ;   gto(G, T, GTO)). % Tail Recursion

ebg(A, Gen, Cond, G_In, G_Mid, T_In, T_Mid) :-
    % For when ChoicePoint should not be carried
    prolog_current_choice(ChoicePoint),
    ebg(A, Gen, Cond, ChoicePoint, G_In, G_Mid, T_In, T_Mid).


ebg(true, true, true, _ChoicePoint, G, G, T, T) :- !.

ebg(!, !, true, ChoicePoint, G, G, T, T) :-
    prolog_cut_to(ChoicePoint).


ebg(Goal, GenGoal, GenGoal, _ChoicePoint, G, G_Out, T, T) :-
    g(GenGoal), !, call(Goal),
    my_append(G, GenGoal, G_Out).

ebg(Goal, GenGoal, GenGoal, _ChoicePoint, G, G, T, T_Out) :-
    t(GenGoal), !, call(Goal),
    my_append(T, GenGoal, T_Out).

%                                   GenVar is GenExpr
ebg(Var is Expr, GenVar is _GenExpr,      true       , _ChoicePoint, G, G, T, T) :- !,
    % To unify the distance variables
    call(Var is Expr),
    GenVar = Var.

ebg(Goal, GenGoal, GenGoal, _ChoicePoint, G, G, T, T) :-
    Goal \= (_, _), Goal \= (_; _), Goal \= (_ -> _),
    predicate_property(Goal, built_in), !,
    call(Goal).


ebg(Goal, GenGoal, Cond, _ChoicePoint, G_In, G_Out, T_In, T_Out) :-
    Goal \= (_, _), Goal \= (_; _), Goal \= (_ -> _),
    prolog_current_choice(ChoicePoint),
    clause(GenGoal, GenBody),
    copy_term((GenGoal :- GenBody), (Goal :- Body)),
    ebg(Body, GenBody, Cond, ChoicePoint, G_In, G_Out, T_In, T_Out).


ebg((A, B), (GenA, GenB), Cond, ChoicePoint, G_In, G_Out, T_In, T_Out) :-
    ebg(A, GenA, CondA, ChoicePoint, G_In, G_Mid, T_In, T_Mid),
    ebg(B, GenB, CondB, ChoicePoint, G_Mid, G_Out, T_Mid, T_Out),
    simplify((CondA, CondB), Cond).

ebg((A -> B), (GenA -> GenB), Cond, ChoicePoint, G_In, G_Out, T_In, T_Out) :-
    ebg(A, GenA, CondA, G_In, G_Mid, T_In, T_Mid), !,
    ebg(B, GenB, CondB, ChoicePoint, G_Mid, G_Out, T_Mid, T_Out),
    simplify((CondA -> CondB), Cond).

ebg((A -> B; _), (GenA -> GenB), Cond, ChoicePoint, G_In, G_Out, T_In, T_Out) :-
    ebg(A, GenA, CondA, G_In, G_Mid, T_In, T_Mid), !,
    ebg(B, GenB, CondB, ChoicePoint, G_Mid, G_Out, T_Mid, T_Out),
    simplify((CondA -> CondB), Cond).

ebg((_ -> _; C), GenC, CondC, ChoicePoint, G_In, G_Out, T_In, T_Out) :- !,
    ebg(C, GenC, CondC, ChoicePoint, G_In, G_Out, T_In, T_Out).

ebg((A; B), (GenA; GenB), Cond, ChoicePoint, G_In, G_Out, T_In, T_Out) :-
    (   ebg(A, GenA, CondA, ChoicePoint, G_In, G_Out, T_In, T_Out)
    ;   ebg(B, GenB, CondB, ChoicePoint, G_In, G_Out, T_In, T_Out)
    ),
    simplify((CondA; CondB), Cond).

% Simplifies the generalization when necessary.
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
%   Variable Inversion
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

invert_variables_in_list(VarsList1, VarsList2, OriginalGoalList, InvertedGoalList) :-
    % 1. Creates the bidirectional mapping for swapping (e.g., [A/E, E/A, ...])
    create_bidirectional_mapping(VarsList1, VarsList2, Mapping),

    % 2. Processes the goal list to generate the inverted list
    swap_variables_goal_list(Mapping, OriginalGoalList, InvertedGoalList).

swap_variables_goal_list(_, [], []) :- !.
swap_variables_goal_list(Mapping, [Goal | Goals], [NewGoal | NewGoals]) :-
    % For each goal, swap its internal variables recursively.
    swap_terms(Mapping, Goal, NewGoal),
    swap_variables_goal_list(Mapping, Goals, NewGoals).

create_bidirectional_mapping([], [], []) :- !.
create_bidirectional_mapping([H1|T1], [H2|T2], [H1/H2, H2/H1 | RestMapping]) :-
    create_bidirectional_mapping(T1, T2, RestMapping).

find_substitute(Term, [Key/Value | _], Value) :-
    same_term(Term, Key), !.
find_substitute(Term, [Key/Value | _], Key) :-
    same_term(Term, Value), !.
find_substitute(Term, [_|Tail], Substitute) :-
    find_substitute(Term, Tail, Substitute).

swap_terms(Mapping, Term, Substitute) :-
    var(Term),
    !,
    (   find_substitute(Term, Mapping, Substitute) -> true
    ;   Substitute = Term
    ).
    
swap_terms(_, Term, Term) :-
    atomic(Term), !.
swap_terms(Mapping, CompoundTerm, NewCompoundTerm) :-
    CompoundTerm =..
