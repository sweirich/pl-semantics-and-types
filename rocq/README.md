# Rocq Development overview

- common
  * [common.core](common/core.v)
    Autosubst core definitions 
  * [common.fintype](common/fintype.v)
    Autosubst fin type
  * [common.fin_util](common/fin_util.v)
    Additional properties of fin type
  * [common.renaming](common/renaming.v)
    Language independent lemmas about renamings
  * [common.relations](common/relations.v)x
    Multistep reduction

- STLC: Simply Typed Lambda Calculus
  * stlc/syntax.sig
    Autosubst input
  * [stlc.syntax](stlc/syntax.v)
    Definition of the syntax (generated)
  * [stlc.typing](stlc/typing.v)
    Typing relation
  * [stlc.red](stlc/red.v)
    Small-step and big-step operational semantic
  * [stlc.safety](stlc/safety.v)
    Preservation and progress
  * [stlc.small_step](stlc/small_step.v)
    Properties of small-step and multistep evaluation
  * [stlc.red_equiv](stlc/red_equiv.v)
    Equivalence between small-step and big-step
  * [stlc.soundness](stlc/soundness.v)
    Termination (totality) for of big-step semantics

- REC: Fine-grained CBV with recursive values and recursive types
  * [syntax.sig](rec/syntax.sig)
    Autosubst input for terms
  * [rec.syntax](rec/syntax.v)
    Generate term syntax
  * [rec.typesyntax](rec/typesyntax.sig) 
    Autosubst input for types
  * [rec.typesyntax](rec/typesyntax.v)
    Generate type syntax
  * [rec.reduction](rec/reduction.v)
    Small-step operational semantics. Includes some notes about Autosubst and 
    various properties of the small-step relation.
  * [rec.typing](rec/typing.v)
    Typing relation, preservation and progress proofs
  * [rec.extensions](rec/extensions.v)
    Derived syntactic forms for fine-grained CBV
  * [rec.semsound](rec/semsound.v)
    Cannot show termination for multistep evaluation (incomplete proof)
  * [rec.iprop](rec/iprop.v)
    propositions indexed by steps
  * [rec.stepsLR](rec/stepsLR.v)
    Definition of step-indexed logical relation via strong induction (requires proof irrelevance)
  * [rec.steps](rec/steps.v)
    Proof of semantic soundness for step-indexed logical relation

