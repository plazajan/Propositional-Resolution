c :- consult(resolution0).

/*
Propositional theorem prover -
resolution with pure literal and subsumption elimination, 
implemented in ISO Prolog.
Educational software.
Version of 2023/03/11

https://github.com/plazajan
                    
Copyright 1987-2023, Jan A. Plaza

This file is part of Prolog-Propositinal-Resolution. 
Prolog-Propositinal-Resolution is free software: 
you can redistribute it and/or modify it under the terms of 
the GNU General Public License as published by the Free Software Foundation,
either version 3 of the License, or (at your option) any later version. 
Prolog-Propositinal-Resolution is distributed in the hope that it will be 
useful, but WITHOUT ANY WARRANTY; 
without even the implied warranty of MERCHANTABILITY 
or FITNESS FOR A PARTICULAR PURPOSE. 
See the GNU General Public License for more details. 
You should have received a copy of the GNU General Public License 
along with Prolog-Propositinal-Resolution. 
If not, see https://www.gnu.org/licenses/.

****************************************************************************
****************************************************************************
******                                                                ******
******                   PROPOSITIONAL RESOLUTION                     ******
******                                                                ******
******                        Jan A. Plaza                            ******
******                                                                ******
******                     1987, revised 3/2023                       ******
******                                                                ******
****************************************************************************
****************************************************************************
*/

/*
****************************************************************************
SET AND LIST OPERATIONS                                                        
****************************************************************************

A *set* is a sorted list without duplicates (sorted by Prolog's @<.)
This is a canonical representation of a set as in mathematics - of a collection
of elements without duplicates, whose order does not matter.
Two sets are defined to be equal if they contain the same elements.
Names of procedures/operations on the domain of sets begin with 's_'. 
Arguments of such procedures and the values they return are sets.
(Later, clauses will be sets -- sorted lists, no duplicates.)

Elements of sets and osets are arbitrary ground terms.  
Two elements are equal if they are egual in the sense of Prolog's == ,
so 2+1 and 3 are different.

Testing if two sets have the same elements is Theta(n),
while testing if two lists have the same elements is O(n log n).
The same about testing if a set is a subset of another.
*/

% memberGen(++List, -*Item) finite terminating/closed generator -
% each redo terminates (last redo fails).
% Works for any list, including sets and osets.
memberGen(List, Item) :-
    member(Item, List).
    
% memberRemainderGen(++List, -*Item, -*Remainder) finite terminating/closed 
% generator -
% each redo terminates (last redo fails).
% Remainder is List with Item removed.
% Works for any list, including sets.
memberRemainderGen([Item|Rest], Item, Rest).
memberRemainderGen([X|Rest], Item, [X|Remainder]) :-
    % Item \== X;
    memberRemainderGen(Rest, Item, Remainder).
    
% memberTest(++Item, ++Oset) test.
% Works for any list, including sets.
memberTest(X, O_Set) :- 
	member(X, O_Set), !.   % the cut makes is a test - no choice point saved.

% s_member(++Item, ++Set) test.
s_member(X, [Y| Rest]) :-
	X @> Y, !,
	s_member(X, Rest).
s_member(X, [X|_Rest]).

% s_add(++Item, ++Set, -ResultSet) function.
s_add(X, [Y|Rest], [Y|NewRest]) :-
	X @> Y, !,
	s_add(X, Rest, NewRest).
s_add(X, [X|Rest], [X|Rest]) :- !. % no duplicates
s_add(X, List, [X|List]).

% s_remove(++Item, ++Set, -ResultSet) function.
s_remove( X, [Y|Rest], [Y|NewRest]) :-
	X@>Y, !,
	s_remove(X, Rest, NewRest).
s_remove( X, [X|Rest], Rest) :- !.
s_remove(_X, List, List).

% s_subset(++Set1, ++Set2) test.
s_subset([X1|Rest1], [X2|Rest2]) :-
	X1 @> X2, !,
	s_subset([X1|Rest1], Rest2).
s_subset([X|Rest1], [X|Rest2]) :-
	s_subset(Rest1, Rest2).
s_subset([], _Set).
    
%s_union(++Set1, ++Set2, -ResultSet) function.
s_union([X1|Rest1], [X2|Rest2], [X1|NewRest]) :-
	X1 @< X2, !,
	s_union(Rest1, [X2|Rest2], NewRest).
s_union([X1|Rest1], [X2|Rest2], [X2|NewRest]) :-
	X1 @> X2, !,
	s_union([X1|Rest1], Rest2, NewRest).
s_union([X|Rest1], [X| Rest2], Result) :- !,
	s_union(Rest1, [X|Rest2], Result).
s_union([], S_Set, S_Set) :- !. % the cut makes it a function - no choice point.
s_union(S_Set, [], S_Set).

/*
****************************************************************************
SUBSUMPTION AND ANTICHAINS
****************************************************************************

Subsumption is a concept concerning clauses (sets of literals),
but in the propositional case, it is purely set theoretical - 
it does not depend on the nature of the elements of such sets, 
and we use it here for sets of arbitrary elements.

Clause1 is *subsumed*by* Clause2 iff Clause2 is a subset of Clause1.
Set1    is *subsumed*by* Set2    iff Set2    is a subset of Set1.

A Set is subsumed by a list of sets 
iff it is subsumed by a member of the list.
A Clause is subsumed by a list of clauses 
iff it is subsumed by a member of the list.
(If so, Clause is not needed for the resolution.)

An antichain is a set of sets, where 
no element is a subset of another element, i.e.
every two distinct elements are incomparable by the subset relation.
We will form antichains of clauses. Notice that, in the propositional case,
an antichain of clauses is a set of clauses where no clauses subsumes
another.
*/

% presentIn(++Item, ++ListOfSets) test.
presentIn(Item, ListOfSets) :-
	memberGen(ListOfSets, Set), 
	s_member(Item, Set), !.    % The cut makes it a test.

% subsumed(++Set, ++ListOfSets) test.
% Set is subsumed by ListOfSets.
subsumed(Set1, [ Set2|_Rest]) :-
	s_subset(Set2, Set1), !.
subsumed(Set1, [_Set2|Rest]) :-
	/* \+ s_subset(_Set2, Set1), */
	subsumed(Set1, Rest).

% removeSubsumed(++Set, ++ListOfSets, -ResultListOfSets) function.
% Remove from ListOfSets the clauses subsumed by Set.
removeSubsumed( Set1, [Set2|Rest], NewRest) :-
	s_subset(Set1, Set2), !,
	removeSubsumed(Set1, Rest, NewRest).
removeSubsumed( Set1, [Set2|Rest], [Set2|NewRest]) :-
	% \+ s_subset(Set1, Set2),
	!,
	removeSubsumed(Set1, Rest, NewRest).
removeSubsumed(_Set, [], []).

% addSetToAntiChain(++Set, ++AntiChain, -ResultAntiChain) function.
addSetToAntiChain(Set, AC, AC) :-    % A subsumed Set is not added to AC.
	subsumed(Set, AC), !.
addSetToAntiChain(Set, AC, [Set|NewAC]) :- % When Set is added to AC
	removeSubsumed(Set, AC, NewAC). % subsumed AC members are removed.

% unionWithSubsElim(++ListOfSets, ++AntiChain, -ResultAntiChain)
% function.
unionWithSubsElim([], AC, AC).
unionWithSubsElim([Set|Rest], AC, NewAC) :-
	subsumed(Set, AC), !,
	unionWithSubsElim(Rest, AC, NewAC).
unionWithSubsElim([Set|Rest], AC, [Set|NewRest]) :-
	% \+ subsumed(Set, AC), 
	removeSubsumed(Set, AC, TempAC),
	unionWithSubsElim(Rest, TempAC, NewRest).
	
/*
addSetToAntiChain predicate makes two passes over the antichain (2nd argument),
in the worst case. One could always complete the operation in one pass
if the antichain were sorted by an s2=< total order:

    Set1 s2=< Set2 iff length(Set1) < length(Set2) or
                       (length(Set1) == length(Set2) and Set1 @=< Set2).
                       
This is different from Prolog's standard total order of terms, because
[a,b] @< [c]  while  [c] s2=< [a,b].

An implementation would be straightforward to do in a procedural programming 
language but becomes complicated while using Prolog.
*/
    
/*
****************************************************************************
OPERATORS                                                                 
****************************************************************************

The following operators can be used to build propositional formulas.
Constants 'true', 'false' are also allowed. 

As propositional letters you can use Prolog atoms or numbers.
*/

:- op(130,  fy, not).          
:- op(140, yfx, [and, or, nand, nor]). % left associative
:- op(150, xfy, [imp, nrimp]).         % right associative
:- op(150, yfx, [rimp, nimp, minus]).  % left associative
:- op(160, yfx, [equ, xor]).           % left associative

% yfx - left-asociative:  p and q and r  means  (p and q) and r.
% xfy - right-associative:  p imp q imp r  means  p imp (q imp r)

% not 130 - binds strongest.  equ,xor 160 - bind weakest.
% Every connective has the same precedence and associativity type as its dual.

% nimp is the negated implication.
% minus is an alternative name for nimp;
% p minus q  is equivalent to  p and not q.
% p nimp q   is equivalent to  not (p imp q),  is equivalent to  p and not q.

% rimp is the reversed imp:  p rimp q  is equivalent to  q imp p.

% nrimp is the negated reversed implication.
% p nrimp q  is equivalent to  not (p rimp q),  is equivalent to  q nimp p.

% p nor q   is equivalent to  not (p or  q),  sometimes written as downarrow.
% p nand q  is equivalent to  not (p and q),  sometimes written as uparrow.

% The following unary operators can prefix a formula.
% tautology ++Formula     is a test.
% satisfiable ++Formula   is a test.
% cnf ++Formula           is a success (side-effect: prints CNF).
:-op(650, fx, [tautology, satisfiable, cnf]).

% ++ListOfFormulas consequence ++Formula          is a test.
:-op(660, xfx, consequence).
	
/*
****************************************************************************
FORMULAS                                                                  
****************************************************************************

Every formula is conjunctive or disjunctive or negational or a truthConstant 
or a literal.

A conjunctive formula is equivalent to the conjunction of its components.
A disjunctive formula is equivalent to the disjunction of its components.
A negational formula is equivalent to its component.
The component of truthConstant true is true.
The component of truthConstant false is false.
*/

% conjunctive(++Formula) test.
conjunctive(_ and _).
conjunctive(_ minus _).
conjunctive(_ nimp _).
conjunctive(_ nrimp _).
conjunctive(_ nor _).
conjunctive(_ equ _). % equ will be treated as a conjunction of two imps
conjunctive(not F) :- 
    disjunctive(F).

% disjunctive(++Formula) test.
disjunctive(_ or _).
disjunctive(_ imp _).
disjunctive(_ rimp _).
disjunctive(_ nand _).
disjunctive(_ xor _). % xor will be treated as a disjunction of two nimps
disjunctive(not F) :- 
    conjunctive(F).

% negational(++Formula) test.
% Note:  not p  isn't negational; it is a literal.
negational(not not _) :- !. % double negation
negational(not true) :- !.
negational(not false).

% truthConstant(++Formula) test.
truthConstant(true).
truthConstant(false).

% components(++Formula, -Formula1, -Formula2) function.
% Cuts are used below to make predicates functions (eliminate choice points);
% this is a matter of style, not correctness or efficiency.
components(X and Y, X, Y).
components(not(X and Y), not X, not Y) :- !.
components(X or Y, X, Y).
components(not(X or Y), not X, not Y) :- !.

components(X imp Y, not X, Y).
components(not(X imp Y), X, not Y) :- !.
components(X nrimp Y, not X, Y).
components(not(X nrimp Y), X, not Y) :- !.

components(X minus Y, X, not Y).       % minus is just another name for nimp.
components(not(X minus Y), not X, Y) :- !.
components(X nimp Y, X, not Y).
components(not(X nimp Y), not X, Y) :- !.
components(X rimp Y, X, not Y).
components(not(X rimp Y), not X, Y) :- !.

components(X nand Y, not X, not Y).
components(not(X nand Y), X, Y) :- !.
components(X nor Y, not X, not Y).
components(not(X nor Y), X, Y) :- !.

components(X equ Y, X imp Y, Y imp X).
components(not(X equ Y), X nimp Y, Y nimp X) :- !.
components(X xor Y, X nimp Y, Y nimp X).
components(not(X xor Y), X imp Y, Y imp X).

% component(++Formula, -Component) function.
component(not not X, X) :- !.
component(not true, false) :- !.
component(not false, true).

component(true, true).
component(false, false).

% makeConjunction(++ListOfFormulas, -Conjunction) function.
makeConjunction([], true) :- !.
makeConjunction([Formula], Formula) :- !.
makeConjunction([Formula | Rest], Formula and Temp) :- 
    makeConjunction(Rest, Temp).

/*
******************************************************************************
CLAUSE MANIPULATION  
******************************************************************************

A clause is a disjunction of literals.
In this program a clause is represented as a set of literals,
i.e. as a sorted list without duplicates.
A generalized clause - gclause - allows arbitrary formulas, not just literals.

A lists of clauses represents a conjunction.
In this program a list of clauses is an oset (ordered set), 
which satisfies an additional condition: no clause subsumes another.
*/

% addToGClause(++Formula, ++GClause, -ResultGClause) function.
% This procedure is used only in the definition of the procedure cnf.
% NOTE: we add  (p and q)  to a gclause, even if it contains  (q and p),
% but the cnf procedure will take care of that.
addToGClause(false, GClause, GClause) :- !.
addToGClause(true, _GClause, [true]) :- !.
addToGClause(_, [true], [true]) :- !.
addToGClause(not X, GClause, [true]) :-
	s_member(X, GClause), !.
addToGClause(X, GClause, [true]) :- 
	s_member(not X, GClause), !.   
addToGClause(X, GClause, NewGClause) :-
	s_add(X, GClause, NewGClause).

% addGClauseToAntiChain(++GClause, ++ListOfGClauses, -ResultListOfGClauses) function.
% This procedure is used only in the definition of the procedure cnf.
addGClauseToAntiChain( [true], List, List) :- !. % Adding true to a conjunction.
addGClauseToAntiChain( [], _List, [[]]) :- !. % Adding false to a conjunction.
addGClauseToAntiChain(_GClause, [[]], [[]]) :- !. % Adding to false conjunction.
addGClauseToAntiChain(GClause, List, NewList) :-
    addSetToAntiChain(GClause, List, NewList).
    
% addClauseToAntiChain(++Clause, ++ListOfClauses, -ResultListOfClauses) function.
% This procedure is used only in the definition of the procedure newResolvents.
addClauseToAntiChain(Clause, ListOfClauses, ResultListOfClauses) :-
    addGClauseToAntiChain(Clause, ListOfClauses, ResultListOfClauses).

% tautologyReduction(++Clause, -ResultClause) function.
% If Clause contains both  not X  and  X,  reduce Clause to [true].
% Such clauses are never created by addToGClause/3, 
% but can be created in the resolution process, see resolvent/4.
tautologyReduction(Clause, [true]) :-
	memberGen(Clause, not X),
	s_member(X, Clause), !.
tautologyReduction(Clause, Clause).

/*
******************************************************************************
CONJUNCTIVE NORMAL FORM                                                                
******************************************************************************

CNF - conjunction of clauses, i.e. conjunction of disjunctions of literals.
*/

% cnf([[+Formula]], -AntiChainOfClauses) function.
% AntiChainOfClauses is a CNF corresponding to Formula. For representation 
% details, see the introduction to CLAUSE MANIPULATION section.
% Note: cnf([[p and not p]], A) produces A=[[not p],[p]], not A=[[]].
% Note: one can factor out some code to reduce the calls to memberRemaiderGen
% but the code becomes less readable.
cnf([GClause|Rest], ResultList):-
		memberRemainderGen(GClause, Formula, TempGClause),
		(negational(Formula) ; truthConstant(Formula)), !,
    % Needed for truthConstants, even though their components are trivial.
	% Otherwise, we would have cnf([[false]],[[false]]), cnf([[true]],[[true]]),
    % instead of cnf([[false]],[[]]), cnf([[true]],[]).
	component(Formula, NewFormula),
	addToGClause(NewFormula, TempGClause, NewGClause),
	addGClauseToAntiChain(NewGClause, Rest, TempList),
	cnf(TempList, ResultList).
cnf([GClause|Rest], ResultList) :-
		memberRemainderGen(GClause, Alpha, TempGClause),
		conjunctive(Alpha), !,
	components(Alpha, Alpha1, Alpha2),
	addToGClause(Alpha1, TempGClause, NewGClause1),
	addToGClause(Alpha2, TempGClause, NewGClause2),
	addGClauseToAntiChain(NewGClause1, Rest, TempList1),
	addGClauseToAntiChain(NewGClause2, TempList1, TempList),
	cnf(TempList, ResultList).
cnf([GClause|Rest], ResultList) :-
		memberRemainderGen(GClause, Beta, TempGClause0),
		disjunctive(Beta), !,
	components(Beta, Beta1, Beta2),
	addToGClause(Beta1, TempGClause0, TempGClause1),
	addToGClause(Beta2, TempGClause1, NewGClause),
	addGClauseToAntiChain(NewGClause, Rest, TempList),
	cnf(TempList, ResultList).
cnf([Clause|Rest], [Clause|NewRest]) :- % Now, Clause contains only literals.
		% none of the above tests holds, 
	cnf(Rest, NewRest).
cnf([], []).
	
/*
******************************************************************************
PRINTING CNF'S                                                             
******************************************************************************
*/

% cnf(++Formula) success. (side-effect: prints resulting CNF.)
% Can be used as a unary prefix operator. 
% | ?- cnf p and (q or not r).      prints    [q,-r] and [p].
cnf(Formula) :-
    cnf([[Formula]], CNF),
    printCNF(CNF).

% printCNF(++ListOfClauses) success. (side-effect: prints.)
printCNF([]) :- 
    write(true), write('.'), nl.
printCNF([LastClause]) :- !,
    printClause(LastClause), write('.'), nl.
printCNF([Clause|Rest]) :-
    printClause(Clause), write(' and '),
    printCNF(Rest).  

% printClause(++Clause) success. (side-effect: prints.)
printClause([]) :-
    write(false), !.
printClause(Clause) :-
    replaceNots(Clause, AbbrevClause),
    write(AbbrevClause).

% replaceNots(++Clause, -AbbrevClause) function.
% AbbrevClause is like Clause but with -'s replacing not's.
replaceNots([not Literal | Rest], [-Literal | NewRest]) :- !,
    replaceNots(Rest, NewRest).
replaceNots([Literal | Rest], [Literal | NewRest]) :-
    replaceNots(Rest, NewRest).
replaceNots([],[]).

/*
****************************************************************************
PURE LITERAL ELIMINATION
****************************************************************************

If a literal occurs in a list of clauses but the complementary literal does not,
the clause containing the literal is not needed in the resolution
and can be removed from the list.
After the clause is removed, the process needs to be repeated, becasuse the 
clause removal might have caused that another literal to become a pure literal.
*/

% pureLiteralElim(++ListOfClauses, -ResultListOfClauses) function.
pureLiteralElim(List1, List2) :-
	memberRemainderGen(List1, Clause, List0), 
	((memberGen(Clause, not Literal), \+ presentIn(Literal, List0))
	 ;
     (memberGen(Clause,Literal), atom(Literal), \+ presentIn(not Literal,List0))
	), !,
	pureLiteralElim(List0, List2).
pureLiteralElim(List, List). 

/*
****************************************************************************
REFUTATION                                                                
****************************************************************************
*/

% refuted(++AntiChainOfClauses) test.
refuted(AntiChain) :-
	refuted(AntiChain, AntiChain).
	
% refuted(++ListOfClauses1, ++ListOfClauses2) test.
refuted(List, _TotalList) :-
	memberTest([], List), !.
refuted(List, _TotalList) :-
	List=[], !, fail.
refuted(List,  TotalList) :-
    % Invariant: ListAtArgument1 is subsumed by ListAtArgument2.
	newResolvents(List, TotalList, NewList),
	unionWithSubsElim(NewList, TotalList, NewTotalList),
	refuted(NewList, NewTotalList).

% newResolvents(++ListOfClauses1, ++ListOfClauses2, -ResultListOfClauses)
% function.
% ResultListOfClauses contains resolvents obtained by applying the resolution 
% rule to all pairs Clause1, Clause2, where Clause1 in ListOfClauses1 and
% Clause2 in ListOfClauses2.
% Note: There is no need to try to resolve two propositional clauses in 
% multiple ways. If Clause1 and Clause2 can be resolved in two different ways,
% there must be L1, L2 in Clause1 and -L1, -L2 in Clause2, and resolving with 
% respect to either L1 or L2, produces a clause equivalent to [true]. The code 
% below tries only once, and produces [true]. For instance:
% newResolvents([[p,q,r]], [[s,not p,not q]], NewResolventList) 
% produces an empty/true conjunction of clauses: NewResolventList = []. 
newResolvents([], _TotalList, []) :- !.
newResolvents(_List, [], []) :- !.
newResolvents([Clause1|Rest1], [Clause2|Rest2], NewList) :- 
	memberGen(Clause1, X), 
	atom(X), 
	s_member(not X, Clause2), !,
	resolvent(Clause1, Clause2, X, NewClause), 
	newResolvents([Clause1], Rest2, List1), 
	newResolvents(Rest1, [Clause2], List2),
	newResolvents(Rest1, Rest2, List3),
	unionWithSubsElim(List1, List2, NewList1),
	unionWithSubsElim(NewList1, List3, NewList2),
	addClauseToAntiChain(NewClause, NewList2, NewList).
newResolvents([Clause1|Rest1], [Clause2|Rest2], NewList) :- 
	memberGen(Clause1, not X), 
	s_member(X, Clause2), !,
	resolvent(Clause2, Clause1, X, NewClause), 
	newResolvents([Clause1], Rest2, List1), 
	newResolvents(Rest1, [Clause2], List2),
	newResolvents(Rest1, Rest2, List3),
	unionWithSubsElim(List1, List2, NewList1),
	unionWithSubsElim(NewList1, List3, NewList2),
	addClauseToAntiChain(NewClause, NewList2, NewList).
newResolvents([Clause1|Rest1], [Clause2|Rest2], NewList) :- 
	/* none of above, */
	newResolvents([Clause1], Rest2, List1), 
	newResolvents(Rest1, [Clause2], List2),
	newResolvents(Rest1, Rest2, List3),
	unionWithSubsElim(List1, List2, NewList1),
	unionWithSubsElim(NewList1, List3, NewList).

% resolvent(++Clause1, ++Clause2, ++PositiveLiteral, -Resolvent) function
resolvent(Clause1, Clause2, Literal, Resolvent) :-
	s_remove(Literal, Clause1, TempClause1),
	s_remove(not Literal, Clause2, TempClause2), 
	s_union(TempClause1, TempClause2, ResultClause), 
	tautologyReduction(ResultClause, Resolvent).

/*
****************************************************************************
RESOLUTION                                                                 
****************************************************************************
*/

% tautology(++Formula) test.
% Can be used as a unary prefix operator.
tautology(Formula) :-
	cnf([[not Formula]], AntiChain),
	pureLiteralElim(AntiChain, NewAntiChain),
	refuted(NewAntiChain).

% satisfiable(++Formula) test.
% Can be used as a unary prefix operator.
satisfiable(Formula) :- 
    \+ tautology(not Formula).
    
% consequence(++ListOfFormulas, ++Formula) test.
% Tests if Formula is logical consequence of ListOfFormulas.
% Can be used as a binary infix operator.
consequence(ListOfFormulas, Formula) :-
   makeConjunction(ListOfFormulas, Conjunction),
   tautology(Conjunction imp Formula).

/*
****************************************************************************
DEMOS
****************************************************************************
*/

demo :-
nl, nl,
write('                 PROPOSITIONAL THEOREM PROVER                      '),nl,
write('                         Jan A. Plaza                              '),nl,
write('This theorem prover is based on J.A. Robinson''s resolution method' ),nl,
write('augmented with pure literal elimination and subsumption elimination'),nl,
write('For any propositional formula F and list of formulas L, the tests: '),nl,
write('                    |?- tautology F.                               '),nl,
write('                    |?- satisfiable F.                             '),nl,
write('                    |?- L consequence F.                           '),nl,
write('always terminate with an answer yes/no.                            '),nl,
write('You can also print a Conjunctive Normal Form:                      '),nl,
write('                    |?- cnf F.                                     '),nl,
write('The formula F can be built using propositional connectives:        '),nl,
write('     not       (negation)                           '),nl,
write('     and       (conjunction)                        '),nl,
write('     or        (inclusive discjunction)             '),nl,
write('     imp       (implication)                        '),nl,
write('     rimp      (reversed implication)               '),nl,
write('     equ       (equivalence, biconditional)         '),nl,
write('     xor       (exclusive disjunction, not(p equ q))'),nl,
write('     nand      (not(p and q))  - Sheffer''s stroke  '),nl,
write('     nor       (not(p or q))                        '),nl,
write('     nimp      (not(p imp q))                       '),nl,
write('     nrimp     (not(p rimp q))                      '),nl,
write('     minus     (p and not q)  - the same as nimp    '),nl,
write('truth constants: true, false,                       '),nl,
write('and propositional symbols. As propositional symbol use            '),nl,
write('identifiers starting with a lower-case letter.                    '),nl,
    % write('To run this demo once again type: demo.'),
    nl.

demo2 :-
    nl, nl,
    write('Verifying the four Tarski-Bernays-Wajsberg axioms:'), nl,
    write('| ?- tautology  (p imp q) imp ((q imp r) imp (p imp r)).'), nl,
    (tautology( (p imp q) imp ((q imp r) imp (p imp r)) ) 
	    -> write(yes) ; write(no) ), nl,
    write('| ?- tautology  p imp (q imp p).'), nl,
    (tautology( p imp (q imp p) ) 
	    -> write(yes) ; write(no) ), nl,
    write('| ?- tautology  ((p imp q) imp p) imp p.'), 
    write(' % Peirce Law'),nl,
    (tautology( ((p imp q) imp p) imp p ) 
	    -> write(yes) ; write(no) ), nl,
    write('| ?- tautology  false imp p.'), nl,
    (tautology( false imp p ) 
	    -> write(yes) ; write(no) ), nl,
    nl,
    write('| ?- tautology  (p imp q) imp (q imp p).'), write(' % False'), nl,
    (tautology( (p imp q) imp (q imp p) ) 
	    -> write(yes) ; write(no) ), nl,
    write('| ?- tautology  (p imp q) and p and not q.'), write(' % False'), nl,
    (tautology( (p imp q) and p and not q ) 
	    -> write(yes) ; write(no) ), nl, 
    write('| ?- tautology  (p equ q) or (p equ r) or (q equ r).'), 
    write(' % True'), nl,
    (tautology( (p equ q) or (p equ r) or (q equ r) ) 
	    -> write(yes) ; write(no) ), nl,
    % write('To run this demo once again type: demo2'),
    nl.
    
demo3 :-
    nl, nl,
    write('| ?- satisfiable  (p imp q) imp (q imp p).'), write(' % True'), nl,
    (satisfiable( (p imp q) imp (q imp p) ) 
	    -> write(yes) ; write(no) ), nl,
    write('| ?- satisfiable  (p imp q) and p and not q.'), 
    write(' % False'), nl,
    (satisfiable( (p imp q) and p and not q ) 
	    -> write(yes) ; write(no) ), nl, 
    write('| ?- satisfiable  (p equ q) or (p equ r) or (q equ r).'), 
    write(' % True'), nl,
    (satisfiable( (p equ q) or (p equ r) or (q equ r) ) 
	    -> write(yes) ; write(no) ), nl,
    % write('To run this demo once again type: demo3'),
    nl.

demo4 :-
    nl, nl,
    write('| ?- [p imp q, q imp r, r imp p]  consequence  q imp p.'), nl,
    (consequence( [p imp q, q imp r, r imp p],  q imp p ) 
	    -> write(yes) ; write(no) ), nl,
	write('| ?- [p imp q, q imp r]  consequence  r imp p.'), nl,
    (consequence( [p imp q, q imp r],  r imp p ) 
	    -> write(yes) ; write(no) ), nl.
	    
demo5 :-
    nl, nl,
    write('| ?- cnf  p and q and r.'), nl,
    cnf( p and q and r ), nl,
    write('| ?- cnf  p or q or r.'), nl,
    cnf( p or q or r ), nl,
    write('| ?- cnf  p xor q xor r.'), nl,
    cnf( p xor q xor r ), nl,
    write('| ?- cnf  true equ false.'), nl,
    cnf( true equ false ), nl,
    write('| ?- cnf  (p imp q) or (q imp p).'), nl,
    cnf( (p imp q) or (q imp p) ), nl,
    write('| ?- cnf  not ((p imp q) or (q imp p)).'), nl,
    cnf( not((p imp q) or (q imp p)) ), nl,
    % write('To run this demo once again type: demo4'),
    nl, nl.
    
:- initialization(demo).
:- initialization(demo2).
:- initialization(demo3).
:- initialization(demo4).
:- initialization(demo5).

/*
****************************************************************************
****************************************************************************
*/
