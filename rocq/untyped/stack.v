Require Export untyped.prim.

Import SyntaxNotations.
Import Lists.List.ListNotations.
Open Scope list_scope.
Open Scope rec_scope.

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

Module Small.

Local Reserved Notation "m ↦ m'" (at level 70).

Inductive step : machine -> machine -> Prop := 
  | s_prim s e e' : 
    e ~>> e' ->
    (s , e) ↦ (s, e')

  | s_pop s e2 v : 
    (f_let e2 :: s, ret v) ↦ (s, e2[v..])

  | s_push  s e1 e2 : 
    (s , let_ e1 e2 ) ↦ (f_let e2 :: s, e1)
where "m ↦ m'" := (step m m') : rec_scope.
  
Definition irreducible (m : machine) : Prop := 
  forall m', not (m ↦ m').

Lemma deterministic :
  forall m m1 m2, (m ↦ m1) -> (m ↦ m2) -> m1 = m2.
Proof.
  intros m m1 m2 h1 h2. 
  inversion h1; subst; inversion h2; subst; auto.
  all: try match goal with [ H : ret _ ~>> _ |- _ ] => inversion H end.
  all: try match goal with [ H : let_ _ _ ~>> _ |- _ ] => inversion H end.
  eapply primitive_deterministic in H; eauto. subst. auto.
Qed.


Definition halts_n (m : machine) n : Prop := 
  exists v, step_n step n m (nil, ret v).

Definition halts (m : machine) : Prop := 
  exists v, multi step m (nil, ret v).

Lemma halts_reverse_prim s e e' : 
  halts (s, e') ->
  e ~>> e' ->
  halts (s, e).
Proof.
  intros h ss.
  destruct h as [m sn].
  exists m. econstructor; eauto. econstructor; eauto.
Qed.

Lemma halts_reverse m m' : 
  halts m ->
  m' ↦ m ->
  halts m'.
Proof.
  intros h ss.
  destruct h as [k sn].
  exists k. econstructor; eauto. 
Qed.

End Small.

Module Notations.
Infix "↦"  := Small.step (at level 70) : rec_scope.
Infix "↦*" := (multi Small.step) (at level 70) : rec_scope.
End Notations.

Import Notations.

Lemma terminal_halts {v} : 
  Small.halts (nil, ret v).
Proof.
  exists v. eapply ms_refl; eauto.
Qed.

Lemma halts_reverse {m m'}:
  Small.halts m' ->  m ↦ m' ->
  Small.halts m.
Proof.
  intros [v h] ss.
  exists v. econstructor; eauto.
Qed.


Lemma halts_forward {m m'}:
  Small.halts m -> m ↦ m' -> 
  Small.halts m'.
Proof.
  intros h ss.
  inversion h; subst. inversion H; subst. inversion ss. inversion H3.
  apply Small.deterministic with (m1 := e2) in ss; eauto. subst.
  eexists. eauto.
Qed.

Lemma halts_n_forward {m m' k}:
  Small.halts_n m k -> m ↦ m' -> 
  exists j, S j = k /\ Small.halts_n m'  j.
Proof.
  intros h ss.
  inversion h; subst. inversion H; subst. inversion ss. inversion H3.
  apply Small.deterministic with (m1 := e2) in ss; eauto. subst.
  eexists. split; eauto. econstructor; eauto. 
Qed.

Lemma halts_n_reverse {m m' k}:
  Small.halts_n m'  k ->  m ↦ m' ->
  Small.halts_n m (S k).
Proof.
  intros [v h] ss.
  exists v. econstructor; eauto.
Qed.


