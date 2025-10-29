Require Export rec.prim.

Import SyntaxNotations.
Export Lists.List.ListNotations.
Open Scope list_scope.
Open Scope rec_scope.

(** * Refactoring of Small step semantics using primitive reductions *)

Module Small.

Reserved Notation "e1 ~> e2" (at level 70).

Inductive step : Tm 0 -> Tm 0 -> Prop := 
  | s_prim e1 e2 : 
    e1 ~>> e2 -> e1 ~> e2

  | s_letv v e : 
    let_ (ret v) e ~> e [v..]

  | s_let_cong e1 e1' e2 : 
    e1 ~> e1' ->
    let_ e1 e2 ~> let_ e1' e2
where "e1 ~> e2" := (step e1 e2).

Lemma ret_irreducible v : 
  forall e, not (ret v ~> e).
Proof.
  intros e h. inversion h. inversion H. Qed.

Lemma deterministic :
  forall e e1 e2, e ~> e1 -> e ~> e2 -> e1 = e2.
Proof. 
  intros e e1 e2 h1. move: e2.
  induction h1; intros ? h2; inversion h2; subst; eauto.
  eapply primitive_deterministic; eauto.
  all: try match goal with [H : let_ _ _ ~>> _ |- _ ] => inversion H end.
  assert False. eapply ret_irreducible; eauto. done.
  assert False. eapply ret_irreducible; eauto. done.
  erewrite IHh1; eauto.
Qed.

(** This refactored version is equivalent to our prior version *)
Lemma equivalent : 
  forall e e' , e ~> e' <-> rec.reduction.Small.step e e'.
Proof.
  intros e e'.
  split.
  - intro h; induction h; eauto with rec.
    inversion H; eauto with rec.
  - intro h; induction h; eauto using primitive, step.
Qed. 

(** We have a congruence rule for multistep reduction in the RHS of a let *)
Lemma let_cong : 
  forall e1 e1' e2, multi Small.step e1 e1' -> multi Small.step (let_ e1 e2) (let_ e1' e2).
Proof.
  intros e1 e1' e2 h. 
  induction h; eauto using Small.step, multi.
Qed.

End Small.


(** * Refactoring of Big Step semantics *)

Module Big. 

Reserved Notation "e ⇓ v" (at level 70).

Inductive step : Tm 0 -> Val 0 -> Prop := 
  | s_val v : 
    ret v ⇓ v
  | s_prim e1 e2 v : 
    e1 ~>> e2 ->
    e2 ⇓ v ->
    e1 ⇓ v 
  | s_let v1 e1 e2 v : 
    e1 ⇓ v1 ->
    e2 [v1..] ⇓ v ->
    let_ e1 e2 ⇓ v
where "e ⇓ v" := (step e v).

(** The big-step semantics is deterministic *)
Lemma deterministic :
  forall e v1 v2, e ⇓ v1 -> e ⇓ v2 -> v1 = v2.
Proof.
  intros e v1 v2 h1. move: v2.
  induction h1; intros ? h2; inversion h2; subst.
  all: eauto.
  all: try match goal with [ H : ret _ ~>> _ |- _ ] => inversion H end.
  all: try match goal with [ H : let_ _ _ ~>> _ |- _ ] => inversion H end.
  eapply primitive_deterministic in H; eauto. subst.  eauto.
  have EQ: v1 = v0. eapply IHh1_1; eauto. subst.
  eauto.
Qed.

End Big.

(** * Big step is equivalent to small step *)

Lemma step_expansion (e1 e2 : Tm 0) (v : Val 0): 
  Small.step e1 e2 -> Big.step e2 v ->
  Big.step e1 v.
Proof.
(* FILL IN HERE *) Admitted.

Lemma SmallBig : 
  forall e v, multi Small.step e (ret v) -> Big.step e v.
Proof. intros e v h. 
       dependent induction h. 
(* FILL IN HERE *) Admitted.

Lemma BigSmall : 
  forall e v, Big.step e v -> multi Small.step e (ret v).
Proof. 
  intros e v h.
  induction h.
(* FILL IN HERE *) Admitted.

Lemma SmallBig_equivalence : 
  forall e v, Big.step e v <-> multi Small.step e (ret v).
Proof. split. eapply BigSmall; eauto. eapply SmallBig; eauto. Qed.


(** * Semantics based on an abstract machine with an explicit stack *)

(** A frame corresponds to the [let_cong] rule of the small step semantics.
   It remembers that after evaluating [e1] we need to continue with evaluting
   the body of a let expression. This body has a single bound variable. *)

Definition frame   := Frame 0.
Definition stack   := list frame.
Definition machine := (stack * Tm 0)%type.

(** An abstract machine is done evaluating when the stack is empty and 
    the expression is a value. *)
Inductive final : machine -> Prop := 
  | final_machine v :
    final ( [] , ret v ).

Module StackSmall.

Inductive step : machine -> machine -> Prop := 
  | s_prim k e e' : 
    e ~>> e' ->
    step (k , e) (k, e')

  | s_pop k e2 v : 
    step (f_let e2 :: k, ret v) (k, e2[v..])

  | s_push  k e1 e2 : 
    step (k , let_ e1 e2 ) (f_let e2 :: k, e1).
  
Definition irreducible (m : machine) : Prop := 
  forall m', not (step m m').

Lemma deterministic :
  forall m m1 m2, step m m1 -> step m m2 -> m1 = m2.
Proof.
  intros m m1 m2 h1 h2. 
  inversion h1; subst; inversion h2; subst; auto.
  all: try match goal with [ H : ret _ ~>> _ |- _ ] => inversion H end.
  all: try match goal with [ H : let_ _ _ ~>> _ |- _ ] => inversion H end.
  eapply primitive_deterministic in H; eauto. subst. auto.
Qed.

End StackSmall.

Module StackBig.
  
(* Big-step machine semantics *)
Inductive step : machine -> Val 0 -> Prop := 
  | s_final v : 
    step ([], ret v) v

  | s_prim k e e' v : 
    e ~>> e' ->
    step (k, e') v ->
    step (k , e) v

  | s_pop k e2 v1 v : 
    step (k, e2[v1..]) v  ->
    step (f_let e2 :: k, ret v1) v

  | s_push  k e1 e2 v : 
    step (f_let e2 :: k, e1) v ->
    step (k , let_ e1 e2 ) v .

End StackBig.



Module Notations.
Infix "~>" := Small.step (at level 70) : rec_scope.
Infix "~>*" := (multi Small.step) (at level 70) : rec_scope.
Infix "⇓"  := Big.step (at level 70) : rec_scope. 
Infix "↦"  := StackSmall.step (at level 70) : rec_scope.
Infix "↦*"  := (multi StackSmall.step) (at level 70) : rec_scope.
Infix "⇊"  := StackBig.step (at level 70) : rec_scope.   (* \downdownarrows *) 
End Notations.

Import Notations.

(** * Machine semantics is the same as the original semantics *)

Lemma bigstep_completeness e v :
  e ⇓ v -> 
  forall s : stack, (s, e) ↦* (s, ret v).
Proof.
  intro h.
  induction h. 
(* FILL IN HERE *) Admitted.

(* PFPL 28.2 *)
Corollary smallstep_completeness e v: 
  e ~>* (ret v) -> ([], e) ↦* ([], ret v).
Proof.
  intros h.
  generalize ([] : stack).
  apply SmallBig in h.
  eapply bigstep_completeness; auto.
Qed.

Fixpoint unravel (s : stack) (e : Tm 0) : Tm 0 := 
 match s with 
  | [] => e 
  | f_let e2 :: k => unravel k (let_ e e2)
  end.

(** The stack indicates the next reduction step that should happen *)
Lemma stack_cong k e e': 
  (e ~> e') -> unravel k e ~> unravel k e'.
Proof. 
  move: e e'.
  induction k.
  - intros. cbn. done.
  - intros. 
    destruct a. cbn.
    eapply IHk.
    eapply Small.s_let_cong. auto.
Qed.

Lemma unravel_step {k e k' e'} :
  (k, e) ↦ (k', e') -> (unravel k e) ~>* (unravel k' e').
Proof.
  intro h.
  dependent induction h; subst.
  - eapply ms_one. eapply stack_cong. eapply Small.s_prim; auto.
  - cbn. eapply ms_one. eapply stack_cong.  eapply Small.s_letv; eauto.
  - cbn. eapply ms_refl.
Qed.

Lemma unravel_multistep s s' e v: 
  (s, e) ↦* (s', ret v) -> unravel s e ~>* unravel s' (ret v).
Proof.
  intro h. dependent induction h.
  - eapply ms_refl.
  - destruct e2 as [s2 e2].
    specialize (IHh s2 s' e2 v ltac:(eauto) ltac:(eauto)).
    eapply ms_app. eapply unravel_step; eauto.
    eauto.
Qed.
    
Lemma smallstep_soundness e v: 
  ([], e) ↦* ([], ret v) -> e ~>* (ret v).
Proof.
  eapply unravel_multistep; eauto.
Qed.

Lemma small_machine_correctness e v:
  ([], e) ↦* ([], ret v) <-> e ~>* ret v.
Proof.
  split. eapply smallstep_soundness. eapply smallstep_completeness.
Qed.

(** * Big machine correctness *)

Lemma small_big_completeness s e v: 
  (s, e) ↦* ([], ret v) -> (s, e) ⇊ v.
Proof.
  intro h.
  dependent induction h.
  - eapply StackBig.s_final.
  - inversion H; subst.
    + eapply StackBig.s_prim; eauto. 
    + eapply StackBig.s_pop; eauto.
    + eapply StackBig.s_push; eauto.
Qed.    

Lemma small_big_soundness s e v : 
  (s, e) ⇊ v -> (s, e) ↦* ([], ret v).
Proof.
  intro h.
  dependent induction h.
  - eapply ms_refl.
  - eapply ms_trans. eapply StackSmall.s_prim; eauto. eauto.
  - eapply ms_trans. eapply StackSmall.s_pop. eauto.
  - eapply ms_trans. eapply StackSmall.s_push. eauto.
Qed.

Lemma small_big_correctness e v:
  ([], e) ↦* ([], ret v) <-> ([], e) ⇊ v.
Proof.
  split. eapply small_big_completeness. eapply small_big_soundness.
Qed.

Lemma big_correctness e v :
  e ⇓ v <-> ([], e) ⇊ v.
Proof.
  rewrite SmallBig_equivalence. 
  rewrite <- small_big_correctness.
  rewrite small_machine_correctness. done.
Qed.
