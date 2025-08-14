# What is this course all about?

This semester, we are going to consider two big questions that one might ask about programs in a programming language.

**1. When are two programs equivalent?**

This question is the heart of programming language semantics. Our goal is to
understand what programs mean, so understanding when a program is equivalent
to some result of evaluation is a way of defining meaning. 

However, program equivalence is more that that. It is also essential for
software development, for compiler correctness, for program verification, and
for security analysis.

For example, when you refactor a program, you are replacing a part of it with
"equivalent" code: you want the code to still work, but be more general in
some way.  Or when a compiler optimizes your program, it replaces part of the
code with an "equivalent" but faster sequence of instructions.  Program
verification often means showing that code is "equivalent" to some
mathematical specification. And security analysis is showing that code is not
equivalent to programs with certain security flaws.

What makes a good definition
of equivalence? How can we reason about this definition mathematically? How
can we use this definition in practice?

**2. What does it mean to type check a program?**

Many programming languages come with static type systems, such as Rust, Java,
OCaml or Rocq. Where do these type systems come from? What does it mean when a
program type checks?  What does it mean when we say that a language is type
safe? What can can we model using static types? How do types interact with the definition of equivalence?

## How will we study these two questions? 

Studying these two questions is a study in definitions. And constructing definitions involves design work. A given definition may not be intrinsically 
wrong, it just may not be useful. So to evaluate our designs we need to 
identify what we want to do with these definitions and judge them using that 
metric.

In general, we will study these questions using the tools of programming
language theory. This means that we will model idealized versions of
programming languages using mathematical objects and then prove properties
about these definitions, using the techniques such as induction and
coinduction.

## How will we stay grounded? 

Programming language theory can seem both **trivial** (only applying to tiny "toy"
languages) and at the same time **esoteric** (filled with unfamiliar jargon).

Programming languages found "in the wild" are complex and rapidly changing. It can be the work of several years to complete a mathematical specification of a language. A notable example is Andreas Rossberg's work on the semantics of 
WebAssembly, which you can find more about by watching his [keynote from ICFP 23](https://www.youtube.com/watch?v=Lb45xIcqGjg).

While such work is important, it does not suit our purposes. Instead we need
programming language models that we can understand in hours, not years. We
need these models to be representative (i.e. they should describe common
features of many different programming languages) and illustrative (i.e. they
should describe these features independently of other language constructs).
Just as biologist gain understanding through the study of a model organisms
such yeast, nematodes or fruit flies, that capture the essence of cell
biology, neuroscience, and genetics, we will look at model programming
languages that capture the essence of computation, using functions, data
structures, control effects, and mutability.

To make sure that we can transfer what we learn from these essential models,
we will talk about their connection to languages that you already know, their
extension with new features, and their ability to do more than immediately
apparent through macro encoding and compilation. Some properties that we prove
for small languages will immediately transfer to larger contexts. Others
provide a blueprint for how we might redo similar proofs at scale. And still
others don't scale, so we also need to be aware of the limitations of our work
and when we need to adopt new approaches.

The unfamiliar vocabulary of any discipline is a sign of maturity. It means that
researchers have examined and analyzed programming languages for more than
seven decades. In the process they have made discoveries, and communicating
those discoveries requires precise naming and notation. One goal of this
semester is to learn these concepts, along with their unfamiliar names, and
understand how they may be put to use in practice. By the end of the semester,
you should be better equipped to talk about languages and read research papers
about programming language advances.

## What is the role of proof assistants? 

If you have read [Software
Foundations](https://softwarefoundations.cis.upenn.edu/) or have taken [CIS
5000](https://www.seas.upenn.edu/~cis5000/current/index.html), you have
already seen the foundation of our study this semester. And have used the
metalanguage of the Rocq proof assistant to mathematically model small
programming languages, such as the simply-typed lambda calculus.

I am a *strong* believer in the value of these tools. They both solidify your
understanding of the metalogic that we are working in as well as provide
strong confidence in your results and give immediate feedback on your progress. They are also fun to use.

However, this is not a course on the use of proof assistants. The homework
assignments will be in LaTeX and the exams will be on paper. If you have not
used a proof assistant before, you will still get a lot out of this course.

That said, I will ensure that the material we study this semester is amenable
to mechanical development. I will be developing and checking the topics that
we cover throughout the semester using Rocq and will make my code
available. (I hope that I can keep up!) You can use this code as the basis for
the homework assignments and will gladly answer any questions and provide
assistance during office hours. Or, if you would like to translate this code
to another context (i.e. Agda or LEAN), I can also provide assistance.

