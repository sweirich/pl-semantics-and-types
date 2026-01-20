
# Programming Languages: Semantics and Types
CIS 7000-01 Fall 2025

## Course Description

What makes a programming language useful, expressive, safe, or even elegant?
How can we evaluate the features of modern programming languages and
understand what they can do and how they relate? This course takes a
mathematical approach to understanding programming language designs, focusing
on their *dynamic semantics* and *static type systems*. We’ll rigorously define
what programs mean using *operational*, *denotational*, and *relational semantics*,
then dive into the expressive power of *type theories* to provide an abstract
view of computation.


## Course Information 

* *Instructor*: [Stephanie Weirich](http://www.seas.upenn.edu/~sweirich)

* *Meeting Times*: MW 1:45pm-3:14pm (9/03 to 12/8)

* *Location*: 3401 Walnut, 401B

* *Office Hours*: Mondays after class in Levine 510 (starting 9/08)

* *Prerequisites*: We will start from the beginning, so there are no real
  prerequisites. However, we will move quickly, so even if you have seen some
  of this before, we will get to new stuff soon.  Familiarity with basic functional
  programming (e.g. OCaml, Haskell or Rocq) is highly recommended. You should
  be comfortable programming with first-class functions and
  inductive/algebraic datatypes. CIS 5000 is recommended, especially
  familiarity with the basics of the untyped and simply-typed lambda calculus.
  
* [*Syllabus*](syllabus.md)

* [*Website*](https://sweirich.github.io/pl-semantics-and-types/)

* [*Lecture Notes*](notes/plst.pdf)

* [*Proof Scripes*](rocq/README.md)

* [*Course Materials*](https://github.com/sweirich/pl-semantics-and-types/tree/main)
  

##  Topics

* Operational semantics. How do we model a program using an abstract machine?
* Relational semantics. How do we model a program as a logical formula?
* Contextual equivalence. How do we know when two programs are equal?
* How do types interact with semantics? What is semantic soundness?
* Computations are not values. How does evaluation order interact with our models? Where do monads come from?
* Continuations. What is the relationship between type systems and control effects?

