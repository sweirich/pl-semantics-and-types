# Rocq Development overview

- common
  * common/core.v
    Autosubst core definitions
  * common/fintype.v
    Autosubst fin type
  * common/fin_util.v
    Additional properties of fin type
  * common/renaming.v
    Language independent lemmas about renamings
  * common/relations.v
    Multistep reduction

- stlc Simply Typed Lambda Calculus
  * stlc/syntax.sig
  * stlc/syntax.v
    Definition of the syntax
  * stlc/typing.v
    Typing relation
  * stlc/red.v
    Small-step and big-step operational semantic
  * stlc/safety.v
    Preservation and progress
  * stlc/small_step.v
    Properties of small-step and multistep evaluation
  * stlc/red_equiv.v
    Equivalence between small-step and big-step
  * stlc/soundness.v
    Totality of big-step semantics

- rec Fine-grained CBV with recursive values and recursive types
  * rec/syntax.sig
  * rec/syntax.v
    Term syntax
  * rec/typesyntax.sig
  * rec/typesyntax.v
    Type syntax
  * rec/reduction.v
    Small-step operational semantics
  * rec/typing.v
    Typing relation, preservation and progress proofs
  * rec/semsound.v
    Cannot show termination for multistep evaluation (incomplete proof)
  * rec/iprop.v
    downward-closed propositions indexed by steps
  * rec/stepsLR.v
    Definition of step-indexed logical relation via strong induction (requires proof irrelevance)
  * rec/steps.v
    Proof of semantic soundness for step-indexed logical relation

