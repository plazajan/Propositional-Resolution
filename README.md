# Prolog-Propositional-Resolution
 
Propositional theorem prover -  
resolution with pure literal and subsumption elimination  
implemented in ISO Prolog.  
Educational materials.

Version of 2023/03/11

https://github.com/plazajan
                    
Copyright 1987-2023, Jan A. Plaza

Use under Creative Commons Attribution Share-Alike International License 4.0

---

### Instructions

Start Prolog.
Type:

    | ?- consult(resolution0.pro)
    
    | ?- demo.
    
    | ?- demo2.
    
    | ?- demo3.
    
    | ?- demo4.
    
---

For every propositional formula F, the tests:  
                    
    | ?- tautology F.                               
    | ?- satisfiable F.    
                                             
always terminate with an answer yes/no.                            
You can also print a Conjunctive Normal Form:   
                   
    | ?- cnf F.             
                                            
The formula F can be built using propositional connectives:   
     
    not       (negation)                           
    and       (conjunction)                        
    or        (inclusive discjunction)             
    imp       (implication)                        
    rimp      (reversed implication)               
    equ       (equivalence, biconditional)         
    xor       (exclusive disjunction, not(p equ q))
    nand      (not(p and q))  - Sheffer's stroke  
    nor       (not(p or q))                        
    nimp      (not(p imp q))                       
    nrimp     (not(p rimp q))                      
    minus     (p and not q)  - the same as nimp    
     
truth constants: 

    true 
    false   
                        
and propositional symbols. 
As propositional symbol use identifiers starting with a lower-case letter. 

From strongest to weakest:

    not           
    and, or, nand, nor (left associative)
    imp, nrimp         (right associative)
    rimp, nimp, minus  (left associative)
    equ, xor.          (left associative)

Every connective has the same precedence and associativity type as its dual.
       
---

### Sample interactions

    | ?- tautology  (p imp q) imp ((q imp r) imp (p imp r)).
    yes
    
    | ?- tautology  p imp (q imp p).
    yes

    | ?- tautology  ((p imp q) imp p) imp p. % Peirce Law
    yes

    | ?- tautology  false imp p.
    yes
    
    | ?- tautology  (p imp q) imp (q imp p). 
    no

    | ?- tautology  (p imp q) and p and not q. 
    no

    | ?- tautology  (p equ q) or (p equ r) or (q equ r). 
    yes


    | ?- satisfiable  (p imp q) imp (q imp p). 
    yes

    | ?- satisfiable  (p imp q) and p and not q. 
    no

    | ?- satisfiable  (p equ q) or (p equ r) or (q equ r). 
    yes


    | ?- cnf  p and q and r.
    [r] and [q] and [p].

    | ?- cnf  p or q or r.
    [p,q,r].

    | ?- cnf  p xor q xor r.
    [p,-q,-r] and [q,-p,-r] and [r,-p,-q] and [p,q,r].

    | ?- cnf  true equ false.
    false.

    | ?- cnf  (p imp q) or (q imp p).
    true.

    | ?- cnf  not ((p imp q) or (q imp p)).
    [-p] and [q] and [-q] and [p].

---


