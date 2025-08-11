
# Programming Languages: Semantics and Types
CIS 7000-01 Fall 2025

> [!IMPORTANT]
> The first class will be on Wednesday, September 3rd.

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
* *Location*: TBA
* *Office Hours*: TBA
* *Prerequisites*: We will start from the beginning, so there are no real
  prerequisites. However, we will move quickly, so even if you have seen some
  of this before, we will get to new stuff soon.  Familiarity wth functional
  programming (e.g. OCaml, Haskell or Rocq) is highly recommended. You should
  be comfortable programming with first-class functions and
  inductive/algebraic datatypes. CIS 5000 is recommended, especially
  familiarity with the basics of the untyped and simply-typed lambda calculus.
  
* *Textbook*: Lecture notes (in development) will be provided.

## Grading and Assignments

* **Homework (60%)**: There will be approximately five homework assignments
  throughout the semester. These will involve written proofs, with
  opportunities for machine assistance. These assignments are designed to
  solidify your understanding of the core concepts.

* **Midterm Exam (20%)**: 90 minute in-class exam sometime in October.

* **Final Exam (20%)**: 3-hour exam during the final exam period.

## Potential Topics

* Operational semantics (environments, big step semantics, small step semantics)
* Denotational semantics (i.e. interpreting language semantics using type theory, similar to interaction trees than domain theory)
* Contextual equivalence (i.e. can we explain the meanings of programs through equality?)
* How do types interact with semantics? (e.g. normalization-by-evaluation, parametricity?)
* Values vs. computations. How does evaluation order interact with all of this? Especially in the presence of effects? Where do monads come from?
* Continuations. What is the relationship between type systems and control effects?

